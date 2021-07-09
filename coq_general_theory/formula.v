Require Import Floats.
Require Import Strings.String.
Open Scope string_scope.

Inductive RatExpr : Type :=
  | Const:  float -> RatExpr
  | OneVar: string -> RatExpr
  | Sum:    RatExpr -> RatExpr -> RatExpr
  | Sub:    RatExpr -> RatExpr -> RatExpr
  | Mul:    RatExpr -> RatExpr -> RatExpr
  | Div:    RatExpr -> RatExpr -> RatExpr
  | Minus:  RatExpr -> RatExpr.