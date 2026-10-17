import SerrePositivity.DifferentialGraded.Category.Components

/-!
# dg nerve の公開宣言の公理監査

概要：N0 では再利用する既存の Leibniz・結合・単位則を監査する。
方針：各工程で公開宣言の `#print axioms` を追加する。
規約：許される公理は propext・Classical.choice・Quot.sound のみ。
使われ方：対象ビルド後に `lake env lean scripts/audit_dg_nerve.lean` を実行する。
原典：HA Construction 1.3.1.6、Proposition 1.3.1.10。
N0 の紙の計算を Lean で証明したことにはならない。
-/

#print axioms SerrePositivity.DifferentialGraded.differential_compose
#print axioms SerrePositivity.DifferentialGraded.compose_assoc
#print axioms SerrePositivity.DifferentialGraded.differential_unit
#print axioms SerrePositivity.DifferentialGraded.compose_unit
#print axioms SerrePositivity.DifferentialGraded.unit_compose
