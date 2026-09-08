# theorem_lib

Paper2Lean theorem library for formalizing papers on proximal methods, splitting
algorithms, fixed-point algorithms, and related variational analysis. The
repository keeps paper-specific formalizations under `TheoremLib/` and reusable
shared concepts under `Foundation/`.


## Code Statistics

<!-- LOC_STATS:START -->

![foundation_lines](https://img.shields.io/badge/foundation_lines-41025-0f766e?style=flat-square)
![theoremlib_lines](https://img.shields.io/badge/theoremlib_lines-58986-2563eb?style=flat-square)
![total_lines](https://img.shields.io/badge/total_lines-100011-16a34a?style=flat-square)

Counting convention:

- `*_lines` counts every line of a `.lean` file, including comments and
  blank lines; the table's `Code lines` column excludes comments,
  docstrings, and blank lines.
- Refreshed automatically after each push to `main`.

| Directory | `.lean` files | Total lines | Code lines |
| --- | ---: | ---: | ---: |
| Foundation | 52 | 41025 | 31537 |
| TheoremLib | 251 | 58986 | 54546 |
| **Total** | **303** | **100011** | **86083** |

<!-- LOC_STATS:END -->

## Formalization Status

<!-- FORMALIZATION_STATUS:START -->

![papers](https://img.shields.io/badge/papers-10-0f766e?style=flat-square)
![defs_items](https://img.shields.io/badge/defs_items-107-2563eb?style=flat-square)
![proved_theorem-items](https://img.shields.io/badge/proved_theorem--items-139-16a34a?style=flat-square)
![open_theorem-items](https://img.shields.io/badge/open_theorem--items-4-dc2626?style=flat-square)

Counting convention:

- `definition-like items` counts `def_*`, `ext_def_*`, and `algo_*` item
  files.
- `theorem-like items` counts `thm_*`, `lem_*`, `prop_*`, `cor_*`, `rem_*`,
  and their `ext_*` versions.
- An item is marked open if its non-comment, non-string Lean code contains
  `sorry` or `admit`, or declares an `axiom`/`constant` command.
- Display names are `first_author_first_three_title_words_year` (underscore
  joined); authors, titles, and years are read from `papers.json`, and an
  unlisted paper falls back to its directory name.

| No. | Paper | Status | Definition-like items | Theorem-like items |
| ---: | --- | --- | ---: | ---: |
| 1 | [Abbas_Dynamical_systems_and_2015](TheoremLib/Abbas_Dynamical_systems_and_forward_backward_algorithms_2015) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 9](https://img.shields.io/static/v1?label=&message=9&color=2563eb&style=flat-square) | ![proved 29](https://img.shields.io/badge/proved-29-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 2 | [Alvarez_A_second_order_2002](TheoremLib/Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002) | ![in progress](https://img.shields.io/static/v1?label=&message=in%20progress&color=f59e0b&style=flat-square) | ![definition-like 13](https://img.shields.io/static/v1?label=&message=13&color=2563eb&style=flat-square) | ![proved 17](https://img.shields.io/badge/proved-17-16a34a?style=flat-square) ![open 4](https://img.shields.io/badge/open-4-dc2626?style=flat-square) |
| 3 | [Alvarez_Attouch_Inertial_proximal_2001](TheoremLib/Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 4](https://img.shields.io/static/v1?label=&message=4&color=2563eb&style=flat-square) | ![proved 4](https://img.shields.io/badge/proved-4-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 4 | [Alvarez_Minimizing_property_second_2000](TheoremLib/Alvarez_Minimizing_property_second_order_dissipative_2000) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 12](https://img.shields.io/static/v1?label=&message=12&color=2563eb&style=flat-square) | ![proved 11](https://img.shields.io/badge/proved-11-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 5 | [Alvarez_Weak_Convergence_of_2004](TheoremLib/Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 4](https://img.shields.io/static/v1?label=&message=4&color=2563eb&style=flat-square) | ![proved 10](https://img.shields.io/badge/proved-10-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 6 | [Attouch_A_DYNAMICAL_APPROACH_2014](TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 26](https://img.shields.io/static/v1?label=&message=26&color=2563eb&style=flat-square) | ![proved 16](https://img.shields.io/badge/proved-16-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 7 | [Attouch_Adly_Dry_friction_2023](TheoremLib/Attouch_Adly_Dry_friction_dynamics_2023) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 8](https://img.shields.io/static/v1?label=&message=8&color=2563eb&style=flat-square) | ![proved 17](https://img.shields.io/badge/proved-17-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 8 | [Attouch_Fast_convex_optimization_2022](TheoremLib/Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 11](https://img.shields.io/static/v1?label=&message=11&color=2563eb&style=flat-square) | ![proved 10](https://img.shields.io/badge/proved-10-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 9 | [Attouch_Redont_A_New_2007](TheoremLib/Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 9](https://img.shields.io/static/v1?label=&message=9&color=2563eb&style=flat-square) | ![proved 16](https://img.shields.io/badge/proved-16-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 10 | [Beck_Teboulle_FISTA_2009](TheoremLib/Beck_Teboulle_FISTA_2009) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 11](https://img.shields.io/static/v1?label=&message=11&color=2563eb&style=flat-square) | ![proved 9](https://img.shields.io/badge/proved-9-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |

<!-- FORMALIZATION_STATUS:END -->



## Foundation

`Foundation/` contains reusable concepts extracted from the paper
formalizations, including topology, Hilbert-space weak convergence, convexity,
fixed-point theory, set-valued monotone operators, semicontinuity, projection,
and variational-analysis utilities.
