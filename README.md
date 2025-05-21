# Lambda Calculus Interpreter - Lab 3 - Variant 6

## Project structure

- `lambda_calc.py` — Implementation of Lambda Calculus Interpreter including `LambdaVar`, `LambdaAbs`, and `LambdaApp` classes with support for:
  `alpha_conversion`, `beta_reduction`, `eta_reduction`, `normal_order`,
  `applicative_order`, `evaluate`, `to_latex`, `visualize`, and Church encoding.
- `test_lambda_calc.py` — Unit tests for core lambda expression processing and evaluation functions.

## Features

- **parse**
  Parse string input into lambda calculus term structure.
- **pretty**
  Convert term into human-readable string form.
- **alpha_conversion**
  Rename bound variables to avoid naming conflicts.
- **beta_reduction**
  Function application: substitute argument into abstraction.
- **eta_reduction**
  Simplify expressions where applicable.
- **normal_order**
  Reduce the outermost leftmost reducible expression first.
- **applicative_order**
  Evaluate arguments before applying the function.
- **evaluate**
  Perform step-by-step reduction with history tracking.
- **to_latex**
  Convert lambda term into LaTeX format.
- **visualize**
  Render the reduction history using matplotlib with LaTeX.
- **church_n**
  Generate Church-encoded numbers.
- **is_zero**
  Determine if Church numeral is zero.
- **Y_combinator**
  Define the fixed-point combinator for recursion.

## Contribution

- Liu Jiayi — lambda_calc.py.
- Tong Hui — test_lambda_calc.py.

## Changelog

- 20.05.2025 - 2  
  - Add visualization and rendering support via matplotlib.
- 18.05.2025 - 1  
  - Implement beta/eta reduction and parsing support.
- 15.05.2025 - 0  
  - Initial commit with Lambda term structure and base evaluator.
