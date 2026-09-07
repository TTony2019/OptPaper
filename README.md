# theorem_lib

Paper2Lean theorem library for formalizing papers on proximal methods, splitting
algorithms, fixed-point algorithms, and related variational analysis. The
repository keeps paper-specific formalizations under `TheoremLib/` and reusable
shared concepts under `Foundation/`.


## Code Statistics

<!-- LOC_STATS:START -->

![foundation_lines](https://img.shields.io/badge/foundation_lines-41024-0f766e?style=flat-square)
![theoremlib_lines](https://img.shields.io/badge/theoremlib_lines-520699-2563eb?style=flat-square)
![total_lines](https://img.shields.io/badge/total_lines-561723-16a34a?style=flat-square)

Counting convention:

- `*_lines` counts every line of a `.lean` file, including comments and
  blank lines; the table's `Code lines` column excludes comments,
  docstrings, and blank lines.
- Refreshed automatically after each push to `main`.

| Directory | `.lean` files | Total lines | Code lines |
| --- | ---: | ---: | ---: |
| Foundation | 52 | 41024 | 31537 |
| TheoremLib | 6077 | 520699 | 470826 |
| **Total** | **6129** | **561723** | **502363** |

<!-- LOC_STATS:END -->

## Formalization Status

<!-- FORMALIZATION_STATUS:START -->

![papers](https://img.shields.io/badge/papers-175-0f766e?style=flat-square)
![defs_items](https://img.shields.io/badge/defs_items-2520-2563eb?style=flat-square)
![proved_theorem-items](https://img.shields.io/badge/proved_theorem--items-1496-16a34a?style=flat-square)
![open_theorem-items](https://img.shields.io/badge/open_theorem--items-2050-dc2626?style=flat-square)

Counting convention:

- `definition-like items` counts `def_*`, `ext_def_*`, and `algo_*` item
  files.
- `theorem-like items` counts `thm_*`, `lem_*`, `prop_*`, `cor_*`, `rem_*`,
  and their `ext_*` versions.
- An item is marked open if its non-comment Lean code contains `sorry`, `admit`,
  `axiom`, or `constant`.
- Display names are `first_author_first_three_title_words_year` (underscore
  joined); authors, titles, and years are read from `papers.json`, and an
  unlisted paper falls back to its directory name.

| No. | Paper | Status | Definition-like items | Theorem-like items |
| ---: | --- | --- | ---: | ---: |
| 1 | [Abbas_Dynamical_systems_and_2015](TheoremLib/Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 9](https://img.shields.io/static/v1?label=&message=9&color=2563eb&style=flat-square) | ![proved 29](https://img.shields.io/badge/proved-29-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 2 | [Alvarez_A_second_order_2002](TheoremLib/Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002) | ![in progress](https://img.shields.io/static/v1?label=&message=in%20progress&color=f59e0b&style=flat-square) | ![definition-like 13](https://img.shields.io/static/v1?label=&message=13&color=2563eb&style=flat-square) | ![proved 18](https://img.shields.io/badge/proved-18-16a34a?style=flat-square) ![open 2](https://img.shields.io/badge/open-2-dc2626?style=flat-square) |

<!-- FORMALIZATION_STATUS:END -->



## Foundation

`Foundation/` contains reusable concepts extracted from the paper
formalizations, including topology, Hilbert-space weak convergence, convexity,
fixed-point theory, set-valued monotone operators, semicontinuity, projection,
and variational-analysis utilities.
