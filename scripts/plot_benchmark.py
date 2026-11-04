#!/usr/bin/env python3
"""Draw the benchmark `B` of `Challenge.lean` as an SVG figure.

The script evaluates `Erdos1017.benchmark` in floating point, transcribing it
and its parts in `Erdos1017.Benchmark` term by term. Each infimum that defines
a root or an inverse (`sigmaD`, `zC`, `mixedInverse`, `twoHeadInverse`) is the
unique solution on its interval, which Lean proves, so the script finds it by
bisection. It also finds by bisection the density `d_x` at which `W` and `E₂`
cross.

Output: a drawing of `B` on `[0, 1/2]`, colored by the family that attains it:
`B(d) = d` up to `1/4`, the two-head curve `E₂` on `(1/4, d_x)`, and the mixed
curve `W` from `d_x` on, which is the split value from `d₁` on. For comparison
it shows the bound `n²/4` of Erdős, Goodman and Pósa and the normalized bound
`(1 − d)/3` of Král', Lidický, Martins and Pehova and of Blumenthal et al., and
tick marks at `d_x`, `d₁` and the kinks `κ₃`, `κ₄`, `κ₅`. The paper's figure
`paper/benchmark.pdf` shows the same curves and marks.

The figure is an illustration: it is not part of the proof, and nothing in it
is checked in Lean. Before drawing, the script asserts that `B` is continuous
at `1/4` (where both branches give `1/4`), at `d_x` and at `d₁`; that `W` is
continuous at `ε_d` and `E₂` at `ε_c`, which checks `σ_d` and `z_c`; that
`d_x ≈ 0.383783` and `d₁ = 1/2 − (51 − 9√21)/100 ≈ 0.40243`; that
`B(κ_k) = (k − 1)/k³` for `k = 3, …, 6`, where `κ_k = (1 − 1/k²)/2`; and, at
every plotted density in `(1/4, 1/2)`, that `E₂` exceeds `W` exactly below
`d_x` and that `B < (1 − d)/3`. It prints the constants it computes.

Run from the repository root with Python 3 (standard library only):

    python3 scripts/plot_benchmark.py [output.svg]

The default output is `paper/benchmark.svg`.
"""

import math
import sys
from pathlib import Path

DEFAULT_OUTPUT = Path('paper/benchmark.svg')
TOLERANCE = 1e-12
STEP = 1 / 2000

# Canvas and plot area, in SVG units, and the top of the vertical axis.
WIDTH, HEIGHT = 720, 440
LEFT, RIGHT, TOP, BOTTOM = 70, 700, 20, 380
Y_MAX = 0.28

# Ink and series colors.
INK = '#0b0b0b'
SECONDARY = '#52514e'
MUTED = '#898781'
GRID = '#e1e0d9'
BLUE = '#2a78d6'
ORANGE = '#eb6834'
AQUA = '#1baf7a'


def boundary(holds, low, high):
    """The point of `[low, high]` where `holds` stops being true, by bisection."""
    while True:
        middle = (low + high) / 2
        if middle in (low, high):
            return middle
        if holds(middle):
            low = middle
        else:
            high = middle


def split_index(r):
    return max(1, math.ceil((1 - r) / r))


def split_value(r):
    if r == 0:
        return 0.0
    j = split_index(r)
    return (-(2 * j + 1) * r ** 2 + 2 * (j + 1) * r - 1) / (j * (j + 1))


SIGMA_ZERO = (3 + math.sqrt(21)) / 6
EPSILON_STAR = (51 - 9 * math.sqrt(21)) / 100


def mixed_denominator(s):
    return s ** 2 + 8 * s + 2


def mixed_density(s):
    return (2 + 16 * s + 33 * s ** 2 - 15 * s ** 4) / (2 * mixed_denominator(s) ** 2)


def mixed_value(s):
    return ((6 + 46 * s + 85 * s ** 2 - 16 * s ** 3 - 16 * s ** 4)
            / (6 * mixed_denominator(s) ** 2))


def mixed_root_polynomial(s):
    return 29 * s ** 3 - 16 * s ** 2 - 14 * s - 2


SIGMA_D = boundary(lambda s: mixed_root_polynomial(s) < 0, 1, 11 / 10)
EPSILON_D = mixed_density(SIGMA_D)


def mixed_inverse(e):
    return boundary(lambda s: mixed_density(s) > e, SIGMA_D, SIGMA_ZERO)


def mixed_curve(e):
    if e <= EPSILON_STAR:
        return split_value(math.sqrt(2 * e))
    if e <= EPSILON_D:
        return mixed_value(mixed_inverse(e))
    return e


def two_head_denominator(z):
    return z ** 2 + z - 1


def two_head_density(z):
    return z ** 2 * (13 * z ** 2 - 16 * z + 5) / (16 * two_head_denominator(z) ** 2)


def two_head_value(z):
    return two_head_density(z) + ((3 * z - 2) ** 2 * (1 - z) * (3 * z - 1)
                                  / (24 * two_head_denominator(z) ** 2))


def two_head_root_polynomial(z):
    return -95 * z ** 4 + 18 * z ** 3 + 193 * z ** 2 - 168 * z + 40


Z_C = boundary(lambda z: two_head_root_polynomial(z) > 0, 3 / 4, 4 / 5)
EPSILON_C = two_head_density(Z_C)


def two_head_inverse(e):
    return boundary(lambda z: two_head_density(z) > e, 2 / 3, Z_C)


def two_head_curve(e):
    if e == 0:
        return 0.0
    if e <= EPSILON_C:
        return split_value(math.sqrt(2 * e))
    return two_head_value(two_head_inverse(e))


def benchmark(d):
    if d <= 1 / 4:
        return d
    if d < 1 / 2:
        return max(mixed_curve(1 / 2 - d), two_head_curve(1 / 2 - d))
    return 0.0


def two_head_wins(d):
    return two_head_curve(1 / 2 - d) > mixed_curve(1 / 2 - d)


D_X = boundary(two_head_wins, 1 / 4, 1 / 2)
D_1 = 1 / 2 - EPSILON_STAR


def kink(k):
    return (1 - 1 / k ** 2) / 2


def densities(low, high):
    """Densities from `low` to `high`, both included, at most `STEP` apart."""
    count = math.ceil((high - low) / STEP)
    return [low + (high - low) * i / count for i in range(count + 1)]


def check():
    """Assert the numerical facts listed in the module docstring."""
    assert abs(max(mixed_curve(1 / 4), two_head_curve(1 / 4)) - 1 / 4) < TOLERANCE, \
        'B is not continuous at 1/4'
    assert abs(mixed_curve(1 / 2 - D_X) - two_head_curve(1 / 2 - D_X)) < TOLERANCE, \
        'W and E2 do not cross at d_x'
    assert abs(mixed_value(mixed_inverse(EPSILON_STAR))
               - split_value(math.sqrt(2 * EPSILON_STAR))) < TOLERANCE, \
        'B is not continuous at d_1'
    assert abs(mixed_value(SIGMA_D) - EPSILON_D) < TOLERANCE, 'W is not continuous at epsilonD'
    assert abs(two_head_value(Z_C) - split_value(math.sqrt(2 * EPSILON_C))) < TOLERANCE, \
        'E2 is not continuous at epsilonC'
    assert abs(D_X - 0.383783) < 1e-6, f'd_x = {D_X}'
    assert abs(D_1 - 0.40243) < 1e-5, f'd_1 = {D_1}'
    for k in range(3, 7):
        assert abs(benchmark(kink(k)) - (k - 1) / k ** 3) < TOLERANCE, f'B(kappa_{k})'
    for d in densities(1 / 4, 1 / 2)[1:-1]:
        assert two_head_wins(d) == (d < D_X), f'E2 > W fails to match d < d_x at d = {d}'
        assert benchmark(d) < (1 - d) / 3, f'B(d) >= (1 - d)/3 at d = {d}'


def x_of(d):
    return LEFT + (RIGHT - LEFT) * d / (1 / 2)


def y_of(value):
    return BOTTOM - (BOTTOM - TOP) * value / Y_MAX


def path(points, stroke, width, dash=None):
    data = 'M' + ' '.join(f'{x:.1f},{y:.1f}' for x, y in points)
    dashes = f' stroke-dasharray="{dash}"' if dash else ''
    return f'<path d="{data}" stroke="{stroke}" stroke-width="{width}"{dashes}/>'


def curve(low, high, function):
    return [(x_of(d), y_of(function(d))) for d in densities(low, high)]


def text(x, y, content, size=12, anchor='start', fill=INK, rotate=False):
    turn = f' transform="rotate(-90 {x:.1f} {y:.1f})"' if rotate else ''
    return (f'<text x="{x:.1f}" y="{y:.1f}" font-size="{size}" text-anchor="{anchor}" '
            f'fill="{fill}"{turn}>{content}</text>')


def italic(content):
    return f'<tspan font-style="italic">{content}</tspan>'


def subscript(content):
    """A subscript; it must end its `text` element, since it lowers the baseline."""
    return f'<tspan dy="3" font-size="9">{content}</tspan>'


def svg():
    d, f, k, n = italic('d'), italic('f'), italic('k'), italic('n')
    x_ticks = [(0, '0'), (0.1, '0.1'), (0.2, '0.2'), (1 / 4, '1/4'), (0.3, '0.3'),
               (0.4, '0.4'), (1 / 2, '1/2')]
    y_ticks = [(0, '0'), (0.1, '0.1'), (0.2, '0.2'), (1 / 4, '1/4')]
    marks = [(D_X, d + subscript(italic('x'))), (D_1, d + subscript('1'))] + [
        (kink(j), 'κ' + subscript(str(j))) for j in range(3, 6)]
    legend = [(BLUE, f'{italic("B")}({d}) = {d} (bipartite/triangle-free)'),
              (ORANGE, 'two-head branch ' + italic('E') + subscript('2')),
              (AQUA, 'mixed/split branch ' + italic('W'))]
    lines = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{WIDTH}" height="{HEIGHT}" '
        f'viewBox="0 0 {WIDTH} {HEIGHT}" role="img" aria-labelledby="title" '
        'font-family="Helvetica, Arial, sans-serif">',
        '<title id="title">The benchmark B(d) on [0, 1/2]</title>',
        f'<rect width="{WIDTH}" height="{HEIGHT}" fill="#ffffff"/>',
        # Gridlines.
        f'<g stroke="{GRID}" stroke-width="1">',
        *(f'<line x1="{x_of(t):.1f}" y1="{TOP}" x2="{x_of(t):.1f}" y2="{BOTTOM}"/>'
          for t in (0.1, 0.2, 0.3, 0.4)),
        *(f'<line x1="{LEFT}" y1="{y_of(t):.1f}" x2="{RIGHT}" y2="{y_of(t):.1f}"/>'
          for t in (0.1, 0.2)),
        '</g>',
        # Axes, ticks and tick labels.
        f'<g stroke="{MUTED}" stroke-width="1">',
        f'<line x1="{LEFT}" y1="{TOP}" x2="{LEFT}" y2="{BOTTOM}"/>',
        f'<line x1="{LEFT}" y1="{BOTTOM}" x2="{RIGHT}" y2="{BOTTOM}"/>',
        *(f'<line x1="{x_of(t):.1f}" y1="{BOTTOM}" x2="{x_of(t):.1f}" y2="{BOTTOM + 5}"/>'
          for t, _ in x_ticks),
        *(f'<line x1="{LEFT - 5}" y1="{y_of(t):.1f}" x2="{LEFT}" y2="{y_of(t):.1f}"/>'
          for t, _ in y_ticks),
        *(f'<line x1="{x_of(t):.1f}" y1="{BOTTOM}" x2="{x_of(t):.1f}" y2="{BOTTOM - 7}"/>'
          for t, _ in marks),
        '</g>',
        *(text(x_of(t), BOTTOM + 19, label, anchor='middle', fill=SECONDARY)
          for t, label in x_ticks),
        *(text(LEFT - 9, y_of(t) + 4, label, anchor='end', fill=SECONDARY)
          for t, label in y_ticks),
        *(text(x_of(t), BOTTOM - 11, label, size=11, anchor='middle', fill=SECONDARY)
          for t, label in marks),
        text((LEFT + RIGHT) / 2, BOTTOM + 46, f'edge density {d} = {k}/{n}²',
             size=13, anchor='middle'),
        text(24, (TOP + BOTTOM) / 2, f'{italic("B")}({d}) ≈ {f}({n}, {k})/{n}²',
             size=13, anchor='middle', rotate=True),
        # Comparison bounds, with their labels.
        '<g fill="none" stroke-linecap="round">',
        path([(x_of(0), y_of(1 / 4)), (x_of(1 / 2), y_of(1 / 4))], MUTED, 1.25, '6 4'),
        path([(x_of(1 / 4), y_of((1 - 1 / 4) / 3)), (x_of(1 / 2), y_of((1 - 1 / 2) / 3))],
             MUTED, 1.5, '0.1 4'),
        path([(x_of(0.43), y_of(1 / 4) + 26), (x_of(0.45), y_of((1 - 0.45) / 3) - 3)],
             MUTED, 0.75),
        '</g>',
        text(x_of(0.02), y_of(1 / 4) - 7, f'Erdős–Goodman–Pósa: {f} ≤ {n}²/4',
             fill=SECONDARY),
        text(RIGHT - 2, y_of(1 / 4) + 22,
             f'Král’ et al.; Blumenthal et al.: (1 − {d})/3', anchor='end', fill=SECONDARY),
        # The benchmark, one path per family that attains it.
        '<g fill="none" stroke-linecap="round" stroke-linejoin="round">',
        path(curve(0, 1 / 4, benchmark), BLUE, 2.5),
        path(curve(1 / 4, D_X, benchmark), ORANGE, 2.5),
        path(curve(D_X, 1 / 2, benchmark), AQUA, 2.5),
        '</g>',
        # Direct labels and legend.
        text(x_of(0.15) + 8, y_of(0.15) + 16, f'{italic("B")} = {d}'),
        text(x_of(0.33) + 6, y_of(benchmark(0.33)) - 6, italic('E') + subscript('2')),
        text(x_of(0.43) + 6, y_of(benchmark(0.43)) - 6, italic('W')),
        '<g stroke-width="2.5" stroke-linecap="round">',
        *(f'<line x1="{LEFT + 12}" y1="{84 + 18 * i - 4}" x2="{LEFT + 36}" '
          f'y2="{84 + 18 * i - 4}" stroke="{color}"/>' for i, (color, _) in enumerate(legend)),
        '</g>',
        *(text(LEFT + 44, 84 + 18 * i, label) for i, (_, label) in enumerate(legend)),
        '</svg>',
    ]
    return '\n'.join(lines) + '\n'


def main():
    arguments = sys.argv[1:]
    if len(arguments) > 1:
        raise SystemExit('usage: plot_benchmark.py [output.svg]')
    output = Path(arguments[0]) if arguments else DEFAULT_OUTPUT
    check()
    for name, value in [('d_x', D_X), ('d_1', D_1), ('epsilonStar', EPSILON_STAR),
                        ('epsilonC', EPSILON_C), ('epsilonD', EPSILON_D),
                        ('sigmaD', SIGMA_D), ('zC', Z_C)]:
        print(f'{name} = {value:.9f}')
    output.write_text(svg(), encoding='utf-8')
    print(f'wrote {output}')


if __name__ == '__main__':
    main()
