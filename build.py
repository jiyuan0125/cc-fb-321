#!/usr/bin/env python3
"""Build dwd.benefit_ledger and dws.daily_value into warehouse.db.

Layering
--------
dwd.benefit_ledger : one row per (mid, benefit)
    mid, benefit, face, used, amortized_left, status
dws.daily_value    : one row per (day, level)
    day, level, value

Amortization rules
------------------
* Face value amortizes per valid day, valid period = [grant_day, expire_day]
  (both endpoints included).
* ADJUST replaces the face on its event day; the new face drives the daily
  rate from the next day. The valid period is cut into segments, and every
  segment amortizes its opening face (the grant face for the first segment,
  the adjusted face afterwards) over its own valid days. If the benefit is
  written off or recovered mid-segment, the unaccrued part of that segment
  remains in the ledger balance.
* Daily amount = segment face / number of valid days in the segment, rounded
  half-up to the cent; a segment's last day absorbs the rounding residual so
  a full segment sums exactly to its face (a per-event recomputation gives
  the same daily figures).
* USE (write-off) and REVOKE (recovery) still accrue on the action day and
  stop from the next day; whatever was not amortized stays in the ledger
  balance (amortized_left).
* Rerunning overwrites the tables instead of appending a second set of rows.
"""

import argparse
import csv
import sqlite3
from collections import defaultdict
from datetime import datetime, timedelta
from decimal import Decimal, ROUND_HALF_UP

CENT = Decimal("0.01")
TERMINAL_ACTIONS = ("USE", "REVOKE", "EXPIRE")


def parse_day(text):
    return datetime.strptime(text, "%Y-%m-%d").date()


def money(text):
    return Decimal(text)


def half_up_cent(value):
    """Round a Decimal to the cent, halves away from zero."""
    return value.quantize(CENT, rounding=ROUND_HALF_UP)


def load_events(path):
    """Group events per (mid, benefit), preserving CSV order within a group."""
    groups = {}
    order = []
    with open(path, newline="", encoding="utf-8") as fh:
        for line_no, row in enumerate(csv.DictReader(fh), start=2):
            key = (row["mid"], row["benefit"])
            event = {
                "action": row["action"],
                "face": money(row["face"]),
                "grant_day": parse_day(row["grant_day"]),
                "expire_day": parse_day(row["expire_day"]),
                "event_day": parse_day(row["event_day"]),
                "amount": money(row["amount"]),
                "line_no": line_no,
            }
            if key not in groups:
                groups[key] = []
                order.append(key)
            groups[key].append(event)
    return groups, order


def load_levels(path):
    levels = {}
    with open(path, newline="", encoding="utf-8") as fh:
        for row in csv.DictReader(fh):
            levels[row["mid"]] = row["level"]
    return levels


def build_ledger(key, events, level):
    """Return (ledger_row, [(day, cents), ...]) for one (mid, benefit)."""
    mid, benefit = key
    grants = [e for e in events if e["action"] == "GRANT"]
    if len(grants) != 1:
        raise ValueError(f"{mid}/{benefit}: expected one GRANT, got {len(grants)}")
    grant = grants[0]
    grant_day = grant["grant_day"]
    expire_day = grant["expire_day"]
    if grant["event_day"] != grant_day:
        raise ValueError(f"{mid}/{benefit}: GRANT event_day differs from grant_day")

    # Face in force after each ADJUST; same-day ADJUSTs follow CSV order and
    # only the last one of the day survives.
    current_face = grant["face"]
    adjusts_by_day = defaultdict(list)
    terminal = None  # (action, day, amount)
    used_total = Decimal("0")
    for event in events:
        action = event["action"]
        if not (grant_day <= event["event_day"] <= expire_day):
            raise ValueError(f"{mid}/{benefit}: event outside valid period "
                             f"(line {event['line_no']})")
        if action == "GRANT":
            continue
        if action == "ADJUST":
            if event["event_day"] >= expire_day:
                raise ValueError(f"{mid}/{benefit}: ADJUST on/after expire_day")
            adjusts_by_day[event["event_day"]].append(event)
        elif action in TERMINAL_ACTIONS:
            if terminal is not None:
                # The only legal collision is a same-day USE/REVOKE pair;
                # USE wins for the ledger status and the write-off amount.
                if terminal[1] != event["event_day"]:
                    raise ValueError(f"{mid}/{benefit}: two terminal events on "
                                     f"different days (line {event['line_no']})")
                if {terminal[0], action} != {"USE", "REVOKE"}:
                    raise ValueError(f"{mid}/{benefit}: conflicting terminal "
                                     f"events {terminal[0]} and {action} "
                                     f"(line {event['line_no']})")
                if action == "USE":
                    terminal = (action, event["event_day"], event["amount"])
            else:
                terminal = (action, event["event_day"], event["amount"])
            if action == "USE":
                used_total += event["amount"]
        else:
            raise ValueError(f"{mid}/{benefit}: unknown action {action}")

    # An ADJUST replaces the face: each segment starts with the face in force
    # on its first day (the grant face for the first segment, the adjusted
    # face afterwards) and amortizes that balance over its own valid days.
    # On truncation the unaccrued part of the current segment remains as the
    # ledger balance.
    segments = []
    seg_start = grant_day
    last_face = current_face
    for adjust_day in sorted(adjusts_by_day):
        # The old face still drives the accrual on the adjust day itself.
        seg_end = adjust_day
        if seg_end >= seg_start:
            segments.append((seg_start, seg_end, current_face))
        for event in adjusts_by_day[adjust_day]:  # CSV order within the day
            current_face = event["amount"]
            last_face = current_face
        seg_start = adjust_day + timedelta(days=1)
    if seg_start <= expire_day:
        segments.append((seg_start, expire_day, current_face))

    # A benefit without a terminal event simply runs to expiry.
    if terminal is None:
        status = "expired"
        stop_day = expire_day
    else:
        term_action, term_day, _ = terminal
        status = {"USE": "used", "REVOKE": "revoked", "EXPIRE": "expired"}[term_action]
        stop_day = term_day

    daily = []  # (date, Decimal amount in yuan, rounded to the cent)
    amortized_left = Decimal("0")
    for start, end, face in segments:
        if start > stop_day:
            # This segment never began: its opening face stays outstanding.
            amortized_left = face
            break
        segment_days = (end - start).days + 1
        # The daily rate always uses the full segment length; truncation only
        # stops further accrual, it never re-prorates the segment.
        rate = half_up_cent(face / Decimal(segment_days))
        accrual_end = min(end, stop_day)
        cursor = start
        accrued = Decimal("0")
        while cursor < accrual_end:
            daily.append((cursor, rate))
            accrued += rate
            cursor += timedelta(days=1)
        if accrual_end == end:
            # Segment ran its full course: last day absorbs the residual so
            # the segment sums exactly to its opening face.
            daily.append((end, half_up_cent(face - accrued)))
            accrued = face
        else:
            # Truncated by USE/REVOKE on stop_day: that day still accrues the
            # ordinary daily amount, then accrual stops.
            daily.append((accrual_end, rate))
            accrued += rate
        amortized_left = half_up_cent(face - accrued)
        if accrual_end < end:
            break

    if not daily:
        raise ValueError(f"{mid}/{benefit}: no amortization accrued")
    if amortized_left < 0:
        raise ValueError(f"{mid}/{benefit}: negative amortized_left")

    ledger = {
        "mid": mid,
        "benefit": benefit,
        "face": last_face,
        "used": half_up_cent(used_total),
        "amortized_left": amortized_left,
        "status": status,
        "level": level,
    }
    return ledger, daily


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--events", default="data/benefit_events.csv")
    parser.add_argument("--members", default="data/members.csv")
    parser.add_argument("--db", default="warehouse.db")
    parser.add_argument("--report", default="build_report.txt")
    args = parser.parse_args()

    groups, order = load_events(args.events)
    levels = load_levels(args.members)

    ledger_rows = []
    # daily_value aggregation: (day, level) -> cents
    daily_value = defaultdict(lambda: Decimal("0"))
    for key in order:
        mid, _ = key
        if mid not in levels:
            raise ValueError(f"{mid}: missing member record in {args.members}")
        ledger, daily = build_ledger(key, groups[key], levels[mid])
        ledger_rows.append(ledger)
        for day, amount in daily:
            daily_value[(day, ledger["level"])] += amount

    conn = sqlite3.connect(args.db)
    try:
        conn.execute("DROP TABLE IF EXISTS benefit_ledger")
        conn.execute("DROP TABLE IF EXISTS daily_value")
        conn.execute(
            """
            CREATE TABLE benefit_ledger (
                mid             TEXT NOT NULL,
                benefit         TEXT NOT NULL,
                face            REAL NOT NULL,
                used            REAL NOT NULL,
                amortized_left  REAL NOT NULL,
                status          TEXT NOT NULL,
                PRIMARY KEY (mid, benefit)
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE daily_value (
                day    TEXT NOT NULL,
                level  TEXT NOT NULL,
                value  REAL NOT NULL,
                PRIMARY KEY (day, level)
            )
            """
        )
        conn.executemany(
            "INSERT INTO benefit_ledger (mid, benefit, face, used, "
            "amortized_left, status) VALUES (?, ?, ?, ?, ?, ?)",
            [
                (
                    row["mid"],
                    row["benefit"],
                    float(row["face"]),
                    float(row["used"]),
                    float(row["amortized_left"]),
                    row["status"],
                )
                for row in ledger_rows
            ],
        )
        conn.executemany(
            "INSERT INTO daily_value (day, level, value) VALUES (?, ?, ?)",
            [
                (day.isoformat(), level, float(value))
                for (day, level), value in sorted(daily_value.items())
            ],
        )
        conn.commit()
    finally:
        conn.close()

    total_value = sum(daily_value.values(), Decimal("0"))
    with open(args.report, "w", encoding="utf-8") as fh:
        fh.write(f"benefit_ledger {len(ledger_rows)}\n")
        fh.write(f"daily_value {len(daily_value)}\n")
        fh.write(f"摊余总额 {total_value:.2f}\n")


if __name__ == "__main__":
    main()
