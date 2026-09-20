# theorem_lib

Paper2Lean theorem library for formalizing papers on proximal methods, splitting
algorithms, fixed-point algorithms, and related variational analysis. The
repository keeps paper-specific formalizations under `TheoremLib/` and reusable
shared concepts under `Foundation/`.


## Code Statistics

<!-- LOC_STATS:START -->

![foundation_lines](https://img.shields.io/badge/foundation_lines-42327-0f766e?style=flat-square)
![theoremlib_lines](https://img.shields.io/badge/theoremlib_lines-109741-2563eb?style=flat-square)
![total_lines](https://img.shields.io/badge/total_lines-152068-16a34a?style=flat-square)

Counting convention:

- `*_lines` counts every line of a `.lean` file, including comments and
  blank lines; the table's `Code lines` column excludes comments,
  docstrings, and blank lines.
- Refreshed automatically after each push to `main`.

| Directory | `.lean` files | Total lines | Code lines |
| --- | ---: | ---: | ---: |
| Foundation | 56 | 42327 | 32581 |
| TheoremLib | 496 | 109741 | 101118 |
| **Total** | **552** | **152068** | **133699** |

<!-- LOC_STATS:END -->

## Formalization Status

<!-- FORMALIZATION_STATUS:START -->

![papers](https://img.shields.io/badge/papers-20-0f766e?style=flat-square)
![defs_items](https://img.shields.io/badge/defs_items-218-2563eb?style=flat-square)
![proved_theorem-items](https://img.shields.io/badge/proved_theorem--items-277-16a34a?style=flat-square)
![open_theorem-items](https://img.shields.io/badge/open_theorem--items-0-dc2626?style=flat-square)

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
| 2 | [Alvarez_A_second_order_2002](TheoremLib/Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 13](https://img.shields.io/static/v1?label=&message=13&color=2563eb&style=flat-square) | ![proved 20](https://img.shields.io/badge/proved-20-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 3 | [Alvarez_Attouch_Inertial_proximal_2001](TheoremLib/Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 4](https://img.shields.io/static/v1?label=&message=4&color=2563eb&style=flat-square) | ![proved 4](https://img.shields.io/badge/proved-4-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 4 | [Alvarez_Minimizing_property_second_2000](TheoremLib/Alvarez_Minimizing_property_second_order_dissipative_2000) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 12](https://img.shields.io/static/v1?label=&message=12&color=2563eb&style=flat-square) | ![proved 10](https://img.shields.io/badge/proved-10-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 5 | [Alvarez_Weak_Convergence_of_2004](TheoremLib/Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 4](https://img.shields.io/static/v1?label=&message=4&color=2563eb&style=flat-square) | ![proved 10](https://img.shields.io/badge/proved-10-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 6 | [Attouch_A_DYNAMICAL_APPROACH_2014](TheoremLib/Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 26](https://img.shields.io/static/v1?label=&message=26&color=2563eb&style=flat-square) | ![proved 16](https://img.shields.io/badge/proved-16-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 7 | [Attouch_Adly_Dry_friction_2023](TheoremLib/Attouch_Adly_Dry_friction_dynamics_2023) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 8](https://img.shields.io/static/v1?label=&message=8&color=2563eb&style=flat-square) | ![proved 17](https://img.shields.io/badge/proved-17-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 8 | [Attouch_AitMansour_Mazgouri_Monotone_2024](TheoremLib/Attouch_AitMansour_Mazgouri_Monotone_stability_2024) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 15](https://img.shields.io/static/v1?label=&message=15&color=2563eb&style=flat-square) | ![proved 26](https://img.shields.io/badge/proved-26-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 9 | [Attouch_Fast_convex_optimization_2022](TheoremLib/Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 11](https://img.shields.io/static/v1?label=&message=11&color=2563eb&style=flat-square) | ![proved 10](https://img.shields.io/badge/proved-10-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 10 | [Attouch_FINITE_CONVERGENCE_OF_2020](TheoremLib/Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 18](https://img.shields.io/static/v1?label=&message=18&color=2563eb&style=flat-square) | ![proved 13](https://img.shields.io/badge/proved-13-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 11 | [Attouch_Redont_A_New_2007](TheoremLib/Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 9](https://img.shields.io/static/v1?label=&message=9&color=2563eb&style=flat-square) | ![proved 16](https://img.shields.io/badge/proved-16-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 12 | [Baji_Cabot_An_Inertial_2006](TheoremLib/Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 15](https://img.shields.io/static/v1?label=&message=15&color=2563eb&style=flat-square) | ![proved 17](https://img.shields.io/badge/proved-17-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 13 | [Beck_Teboulle_FISTA_2009](TheoremLib/Beck_Teboulle_FISTA_2009) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 11](https://img.shields.io/static/v1?label=&message=11&color=2563eb&style=flat-square) | ![proved 9](https://img.shields.io/badge/proved-9-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 14 | [Bot_Csetnek_An_Inertial_2015](TheoremLib/Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 10](https://img.shields.io/static/v1?label=&message=10&color=2563eb&style=flat-square) | ![proved 14](https://img.shields.io/badge/proved-14-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 15 | [Burachik_Svaiter_Robustness_HPE_2001](TheoremLib/Burachik_Svaiter_Robustness_HPE_2001) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 6](https://img.shields.io/static/v1?label=&message=6&color=2563eb&style=flat-square) | ![proved 13](https://img.shields.io/badge/proved-13-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 16 | [Dong_A_strong_convergence_2017](TheoremLib/Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 6](https://img.shields.io/static/v1?label=&message=6&color=2563eb&style=flat-square) | ![proved 8](https://img.shields.io/badge/proved-8-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 17 | [Guler_New_proximal_point_1992](TheoremLib/Guler_New_proximal_point_algorithms_convex_minimization_1992) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 13](https://img.shields.io/static/v1?label=&message=13&color=2563eb&style=flat-square) | ![proved 22](https://img.shields.io/badge/proved-22-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 18 | [Lorenz_Pock_An_Inertial_2015](TheoremLib/Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 11](https://img.shields.io/static/v1?label=&message=11&color=2563eb&style=flat-square) | ![proved 13](https://img.shields.io/badge/proved-13-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 19 | [Moudafi_Oliny_Splitting_inertial](TheoremLib/Moudafi_Oliny_Splitting_inertial_proximal_monotone_operators) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 8](https://img.shields.io/static/v1?label=&message=8&color=2563eb&style=flat-square) | ![proved 3](https://img.shields.io/badge/proved-3-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |
| 20 | [Nesterov_Accelerated_gradient_1983](TheoremLib/Nesterov_Accelerated_gradient_1983) | ![finished](https://img.shields.io/static/v1?label=&message=finished&color=16a34a&style=flat-square) | ![definition-like 9](https://img.shields.io/static/v1?label=&message=9&color=2563eb&style=flat-square) | ![proved 7](https://img.shields.io/badge/proved-7-16a34a?style=flat-square) ![open 0](https://img.shields.io/badge/open-0-64748b?style=flat-square) |

<!-- FORMALIZATION_STATUS:END -->



## Foundation

`Foundation/` contains reusable concepts extracted from the paper
formalizations, including topology, Hilbert-space weak convergence, convexity,
fixed-point theory, set-valued monotone operators, semicontinuity, projection,
and variational-analysis utilities.
