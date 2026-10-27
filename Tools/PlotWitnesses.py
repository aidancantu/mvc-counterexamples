#!/usr/bin/env python3
"""Render README illustrations from the exact witness coordinates.

Requires numpy, matplotlib, and python-flint. From the repository root, run:
    python Tools/PlotWitnesses.py

This is numerical visualization, not a certificate checker or a Lean proof.
"""

import argparse
import hashlib
import json
from pathlib import Path
import tempfile

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import PowerNorm
import numpy as np
from flint import acb, acb_poly, arb, ctx


ROOT = Path(__file__).resolve().parents[1]
BOUNDS = (-1.02, 0.58, -1.13, 0.47)


def checked_midpoint(value):
    # Demand ample accuracy before converting the enclosing ball to a float.
    if not value.is_finite() or value.rel_accuracy_bits() < 40:
        raise ArithmeticError("Insufficient precision for the plotted value")
    return float(value.mid())


def evaluate(degree, resolution, bits):
    ctx.prec = bits
    rows = json.loads(
        (ROOT / f"witnesses/{degree}/critical_centers.json").read_text()
    )["centers"]
    centers = [acb(arb(x[0]) / x[1], arb(y[0]) / y[1]) for x, y in rows]
    assert len(centers) == degree - 1
    q = acb_poly.from_roots(centers)
    p = q.integral() * (1 / q[0])
    values = p.evaluate(centers, algorithm="fast")
    quotients = np.array(
        [checked_midpoint(abs(v / c)) for v, c in zip(values, centers)]
    )
    print(
        f"Degree {degree}: {len(centers)} critical points; "
        f"|P(c)/c| ranges from {quotients.min():.12f} to {quotients.max():.12f}",
        flush=True,
    )

    xmin, xmax, ymin, ymax = BOUNDS
    x = np.linspace(xmin, xmax, resolution)
    y = np.linspace(ymin, ymax, resolution)
    # A square grid of pixel centers; do not sample exactly at P(0)=0.
    points = [acb(float(a), float(b)) for b in y for a in x]
    background = []
    batch = 512
    for start in range(0, len(points), batch):
        values = p.evaluate(points[start : start + batch], algorithm="fast")
        # Take logs in arbitrary precision, before conversion to float.
        # Raw |P| can overflow a machine float away from the critical points.
        background.extend(
            checked_midpoint((1 + abs(v)).log() / arb(10).log()) for v in values
        )
        if start // batch % 20 == 0:
            print(f"Degree {degree}: background {start}/{len(points)}", flush=True)
    return (
        np.array([complex(float(c.real), float(c.imag)) for c in centers]),
        quotients,
        np.array(background).reshape(resolution, resolution),
    )


def render(degree, centers, quotients, background):
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 11})
    fig = plt.figure(figsize=(8, 9.3), facecolor="white")
    ax = fig.add_axes((0.12, 0.25, 0.82, 0.64))
    image = ax.imshow(
        background,
        origin="lower",
        extent=BOUNDS,
        cmap="Blues",
        vmin=0,
        vmax=800,
        alpha=0.25,
        interpolation="bilinear",
    )
    dots = ax.scatter(
        centers.real,
        centers.imag,
        c=quotients,
        cmap="autumn_r",
        norm=PowerNorm(gamma=0.3, vmin=0.9995, vmax=1.19),
        s=5,
        linewidths=0.12,
        edgecolors="#552814",
        zorder=3,
    )
    ax.axhline(0, color="#8c9ba6", linewidth=0.65, alpha=0.65)
    ax.axvline(0, color="#8c9ba6", linewidth=0.65, alpha=0.65)
    ax.set(xlim=BOUNDS[:2], ylim=BOUNDS[2:], xlabel=r"$\operatorname{Re}(z)$", ylabel=r"$\operatorname{Im}(z)$")
    ax.set_aspect("equal")
    ax.spines[["top", "right"]].set_visible(False)
    ax.spines[["left", "bottom"]].set_color("#a6b1ba")
    fig.text(0.12, 0.955, f"The exact degree-{degree} polynomial", fontsize=18, weight="bold")
    fig.text(0.12, 0.919, f"{degree - 1:,} critical points  ·  P(0) = 0  ·  P′(0) = 1", color="#52616d")

    critical_bar = fig.colorbar(dots, cax=fig.add_axes((0.17, 0.153, 0.72, 0.018)), orientation="horizontal")
    critical_bar.set_ticks([0.9995, 1.001, 1.01, 1.05, 1.10, 1.19])
    critical_bar.set_ticklabels(["0.9995", "1.001", "1.01", "1.05", "1.10", "1.19"])
    critical_bar.set_label(r"Critical-point dots: $|P(c)/c|$ (nonlinear color scale)")
    background_bar = fig.colorbar(image, cax=fig.add_axes((0.17, 0.080, 0.72, 0.018)), orientation="horizontal", extend="max")
    background_bar.set_ticks([0, 200, 400, 600, 800])
    background_bar.set_label(r"Faint blue background: $\log_{10}(1+|P(z)|)$; capped at 800")
    fig.text(0.12, 0.012, "Numerical illustration from exact rational inputs; the Lean theorems establish the bounds.", fontsize=8, color="#65717c")
    destination = ROOT / f"docs/images/polynomial-{degree}.png"
    destination.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(destination, dpi=220)
    plt.close(fig)
    print(f"Saved {destination.relative_to(ROOT)}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, choices=(2650, 2917))
    parser.add_argument("--resolution", type=int, default=160)
    parser.add_argument("--bits", type=int, default=16000)
    args = parser.parse_args()
    for degree in ([args.degree] if args.degree else [2650, 2917]):
        # Keep expensive numerical evaluations outside the repository so that
        # layout changes can be rendered without recalculating the grid.
        digest = hashlib.sha256(
            (ROOT / f"witnesses/{degree}/critical_centers.json").read_bytes()
        ).hexdigest()[:16]
        cache = Path(tempfile.gettempdir()) / (
            f"mvc-plot-{degree}-{digest}-{args.resolution}-{args.bits}-v1.npz"
        )
        if cache.exists():
            with np.load(cache) as saved:
                data = saved["centers"], saved["quotients"], saved["background"]
        else:
            data = evaluate(degree, args.resolution, args.bits)
            np.savez(cache, centers=data[0], quotients=data[1], background=data[2])
        render(degree, *data)


if __name__ == "__main__":
    main()
