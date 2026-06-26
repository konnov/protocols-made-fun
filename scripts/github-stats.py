#!/usr/bin/env python3
"""Plot per-day additions and deletions between two git commits.

The default output is an SVG with green bars above zero for added lines and red
bars below zero for deleted lines, matching the style of Figure 3 in the
ZooKeeper testing post.
"""

from __future__ import annotations

import argparse
import csv
import datetime as dt
import math
import os
import subprocess
import sys
import xml.sax.saxutils
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence


@dataclass(frozen=True)
class DailyStat:
    date: dt.date
    added: int
    deleted: int


def run_git(repo: Path, args: Sequence[str]) -> str:
    try:
        proc = subprocess.run(
            ["git", "-C", str(repo), *args],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except subprocess.CalledProcessError as err:
        detail = err.stderr.strip() or err.stdout.strip()
        raise SystemExit(f"git {' '.join(args)} failed: {detail}") from err
    return proc.stdout


def resolve_commit(repo: Path, commit: str) -> str:
    return run_git(repo, ["rev-parse", "--verify", f"{commit}^{{commit}}"]).strip()


def collect_stats(
    repo: Path,
    start_commit: str,
    end_commit: str,
    pathspecs: Sequence[str],
) -> list[DailyStat]:
    """Return per-day numstat totals for commits in start_commit..end_commit."""
    args = [
        "log",
        "--reverse",
        "--date=short",
        "--format=%x1e%cd",
        "--numstat",
        f"{start_commit}..{end_commit}",
    ]
    if pathspecs:
        args.extend(["--", *pathspecs])

    output = run_git(repo, args)
    totals: dict[dt.date, list[int]] = {}
    current_date: dt.date | None = None

    # Use newline-only splitting: str.splitlines() treats Git's \x1e record
    # separator as a line boundary, which would strip our date marker.
    for line in output.split("\n"):
        if not line:
            continue
        if line.startswith("\x1e"):
            current_date = dt.date.fromisoformat(line[1:])
            totals.setdefault(current_date, [0, 0])
            continue
        if current_date is None:
            continue

        fields = line.split("\t", 2)
        if len(fields) < 2:
            continue
        added, deleted = fields[0], fields[1]
        if added == "-" or deleted == "-":
            continue
        totals[current_date][0] += int(added)
        totals[current_date][1] += int(deleted)

    return [
        DailyStat(date=date, added=values[0], deleted=values[1])
        for date, values in sorted(totals.items())
    ]


def write_csv(stats: Sequence[DailyStat], output: Path) -> None:
    with output.open("w", newline="", encoding="utf-8") as out:
        writer = csv.writer(out)
        writer.writerow(["date", "lines_added", "lines_deleted"])
        for stat in stats:
            writer.writerow([stat.date.isoformat(), stat.added, stat.deleted])


def date_range(stats: Sequence[DailyStat]) -> list[dt.date]:
    if not stats:
        return []
    start = stats[0].date
    end = stats[-1].date
    days = (end - start).days
    return [start + dt.timedelta(days=offset) for offset in range(days + 1)]


def nice_step(value: float) -> float:
    if value <= 0:
        return 1
    exponent = math.floor(math.log10(value))
    fraction = value / (10**exponent)
    for candidate in (1, 2, 5, 10):
        if fraction <= candidate:
            return candidate * (10**exponent)
    return 10 ** (exponent + 1)


def y_ticks(max_added: int, max_deleted: int, target_ticks: int = 7) -> tuple[list[int], int, int]:
    low = -max_deleted
    high = max_added
    if low == 0 and high == 0:
        return [-1, 0, 1], -1, 1

    span = high - low
    step = int(nice_step(span / max(1, target_ticks - 1)))
    y_min = int(math.floor(low / step) * step)
    y_max = int(math.ceil(high / step) * step)
    if y_min == y_max:
        y_min -= step
        y_max += step
    if y_min > 0:
        y_min = 0
    if y_max < 0:
        y_max = 0

    ticks = list(range(y_min, y_max + step, step))
    return ticks, y_min, y_max


def choose_date_ticks(days: Sequence[dt.date], target_ticks: int = 7) -> list[dt.date]:
    if not days:
        return []
    if len(days) <= target_ticks:
        return list(days)

    step = max(1, round((len(days) - 1) / (target_ticks - 1)))
    ticks = [days[index] for index in range(0, len(days), step)]
    if ticks[-1] != days[-1]:
        ticks.append(days[-1])
    return ticks


def svg_text(
    x: float,
    y: float,
    text: str,
    *,
    size: int = 16,
    anchor: str = "middle",
    rotate: float | None = None,
    weight: str | None = None,
) -> str:
    attrs = [
        f'x="{x:.2f}"',
        f'y="{y:.2f}"',
        f'font-size="{size}"',
        f'text-anchor="{anchor}"',
    ]
    if rotate is not None:
        attrs.append(f'transform="rotate({rotate:.2f} {x:.2f} {y:.2f})"')
    if weight is not None:
        attrs.append(f'font-weight="{weight}"')
    escaped = xml.sax.saxutils.escape(text)
    return f"<text {' '.join(attrs)}>{escaped}</text>"


def render_svg(stats: Sequence[DailyStat], output: Path) -> None:
    width = 1800
    height = 600
    margin_left = 120
    margin_right = 45
    margin_top = 55
    margin_bottom = 85
    plot_width = width - margin_left - margin_right
    plot_height = height - margin_top - margin_bottom

    days = date_range(stats)
    by_date = {stat.date: stat for stat in stats}
    max_added = max((stat.added for stat in stats), default=0)
    max_deleted = max((stat.deleted for stat in stats), default=0)
    ticks, y_min, y_max = y_ticks(max_added, max_deleted)

    def x_for(day: dt.date) -> float:
        if len(days) <= 1:
            return margin_left + plot_width / 2
        return margin_left + ((day - days[0]).days / (len(days) - 1)) * plot_width

    def y_for(value: float) -> float:
        return margin_top + ((y_max - value) / (y_max - y_min)) * plot_height

    day_step = plot_width / max(1, len(days) - 1)
    bar_width = min(26, max(3, day_step * 0.75))
    zero_y = y_for(0)

    elements: list[str] = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        "<style>"
        "text{font-family:Arial,Helvetica,sans-serif;fill:#000}"
        ".axis{stroke:#000;stroke-width:1.4}"
        ".tick{stroke:#000;stroke-width:1}"
        ".grid{stroke:#ddd;stroke-width:.8}"
        "</style>",
        '<rect width="100%" height="100%" fill="white"/>',
        svg_text(width / 2, 26, "Lines added / deleted per day", size=28),
    ]

    # Plot frame.
    elements.append(
        f'<rect x="{margin_left}" y="{margin_top}" width="{plot_width}" height="{plot_height}" '
        'fill="none" class="axis"/>'
    )

    # Y ticks and labels.
    for tick in ticks:
        y = y_for(tick)
        elements.append(
            f'<line x1="{margin_left - 7}" y1="{y:.2f}" x2="{margin_left}" y2="{y:.2f}" class="tick"/>'
        )
        if tick != 0:
            elements.append(
                f'<line x1="{margin_left}" y1="{y:.2f}" x2="{width - margin_right}" y2="{y:.2f}" class="grid"/>'
            )
        elements.append(svg_text(margin_left - 16, y + 5, str(tick), size=23, anchor="end"))

    # Strong zero line.
    elements.append(
        f'<line x1="{margin_left}" y1="{zero_y:.2f}" x2="{width - margin_right}" y2="{zero_y:.2f}" class="axis"/>'
    )

    # X ticks and labels.
    for tick_day in choose_date_ticks(days):
        x = x_for(tick_day)
        elements.append(
            f'<line x1="{x:.2f}" y1="{height - margin_bottom}" x2="{x:.2f}" '
            f'y2="{height - margin_bottom + 7}" class="tick"/>'
        )
        elements.append(
            svg_text(
                x - 4,
                height - margin_bottom + 46,
                tick_day.isoformat(),
                size=23,
                rotate=-20,
            )
        )

    elements.append(svg_text(22, height / 2, "Lines of code", size=23, rotate=-90))

    # Bars.
    for day in days:
        stat = by_date.get(day, DailyStat(day, 0, 0))
        x = x_for(day) - bar_width / 2
        if stat.added:
            y = y_for(stat.added)
            elements.append(
                f'<rect x="{x:.2f}" y="{y:.2f}" width="{bar_width:.2f}" '
                f'height="{zero_y - y:.2f}" fill="green"/>'
            )
        if stat.deleted:
            y = y_for(-stat.deleted)
            elements.append(
                f'<rect x="{x:.2f}" y="{zero_y:.2f}" width="{bar_width:.2f}" '
                f'height="{y - zero_y:.2f}" fill="red"/>'
            )

    # Legend.
    legend_x = width - margin_right - 220
    legend_y = margin_top + 10
    elements.append(
        f'<rect x="{legend_x}" y="{legend_y}" width="200" height="70" '
        'rx="3" ry="3" fill="white" stroke="#d3d3d3" stroke-width="1.5"/>'
    )
    elements.append(f'<rect x="{legend_x + 15}" y="{legend_y + 13}" width="42" height="16" fill="green"/>')
    elements.append(svg_text(legend_x + 75, legend_y + 29, "lines added", size=22, anchor="start"))
    elements.append(f'<rect x="{legend_x + 15}" y="{legend_y + 43}" width="42" height="16" fill="red"/>')
    elements.append(svg_text(legend_x + 75, legend_y + 59, "lines deleted", size=22, anchor="start"))

    elements.append("</svg>")
    output.write_text("\n".join(elements) + "\n", encoding="utf-8")


def render_png(stats: Sequence[DailyStat], output: Path) -> None:
    try:
        import matplotlib.dates as mdates
        import matplotlib.pyplot as plt
    except ModuleNotFoundError as err:
        raise SystemExit(
            "PNG output requires matplotlib. Install it or use an .svg output path."
        ) from err

    days = date_range(stats)
    by_date = {stat.date: stat for stat in stats}
    added = [by_date.get(day, DailyStat(day, 0, 0)).added for day in days]
    deleted = [-by_date.get(day, DailyStat(day, 0, 0)).deleted for day in days]

    fig, axis = plt.subplots(figsize=(18, 6))
    axis.bar(days, added, color="green", label="lines added")
    axis.bar(days, deleted, color="red", label="lines deleted")
    axis.axhline(0, color="black", linewidth=1.0)
    axis.set_title("Lines added / deleted per day")
    axis.set_ylabel("Lines of code")
    axis.legend(loc="upper right")
    axis.xaxis.set_major_formatter(mdates.DateFormatter("%Y-%m-%d"))
    fig.autofmt_xdate(rotation=20, ha="right")
    fig.tight_layout()
    fig.savefig(output, dpi=100)


def print_summary(stats: Sequence[DailyStat], start_commit: str, end_commit: str) -> None:
    added = sum(stat.added for stat in stats)
    deleted = sum(stat.deleted for stat in stats)
    days_with_commits = len(stats)
    print(f"range: {start_commit}..{end_commit}")
    print(f"days with commits: {days_with_commits}")
    print(f"lines added: {added}")
    print(f"lines deleted: {deleted}")


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate GitHub-style additions/deletions statistics between two commits.",
    )
    parser.add_argument("repo", type=Path, help="git repository path")
    parser.add_argument("start_commit", help="older commit; excluded from the range")
    parser.add_argument("end_commit", help="newer commit; included in the range")
    parser.add_argument(
        "-o",
        "--output",
        default=Path("git_stats_lines.svg"),
        type=Path,
        help="output plot path; .svg is dependency-free, .png requires matplotlib",
    )
    parser.add_argument("--csv", type=Path, help="optional CSV output path")
    parser.add_argument(
        "--path",
        action="append",
        default=[],
        metavar="PATHSPEC",
        help="limit statistics to a git pathspec; can be passed multiple times",
    )
    parser.add_argument(
        "--summary",
        action="store_true",
        help="print total lines added/deleted after writing outputs",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str]) -> int:
    args = parse_args(argv)
    repo = args.repo.resolve()
    start_commit = resolve_commit(repo, args.start_commit)
    end_commit = resolve_commit(repo, args.end_commit)
    stats = collect_stats(repo, start_commit, end_commit, args.path)

    output = args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    suffix = output.suffix.lower()
    if suffix == ".csv":
        write_csv(stats, output)
    elif suffix == ".png":
        render_png(stats, output)
    elif suffix == ".svg" or suffix == "":
        render_svg(stats, output)
    else:
        raise SystemExit(f"unsupported output extension {suffix!r}; use .svg, .png, or .csv")

    if args.csv:
        args.csv.parent.mkdir(parents=True, exist_ok=True)
        write_csv(stats, args.csv)

    if args.summary:
        print_summary(stats, start_commit[:12], end_commit[:12])

    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except BrokenPipeError:
        os._exit(1)
