module
public import SerrePositivity.KST.Comparison.BarSegal
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.Algebra.Category.MonCat.FilteredColimits

/-!
# 対角 bar の有限個のモノイド座標と順序余極限

概要：bar の各次数の有限個の座標を有限表示対象の共変 Hom と比較する。
方針：一対象圏の射列の実 Segal 同型と有限型の表示可能性を使う。
規約：KST Proposition 4.14、SW92 Lemma 1.4 の有限 rank の代表。
使われ方：実 bar と通常の rank 余極限の交換。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits Opposite
attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- 概要：有限個の座標の共変 Hom 関手は自然数添字の余極限を保つ。
方針：有限型の ℵ₀ 表示可能性から filtered colimit 保存を最小添字宇宙へ移す。
規約：SW92 Lemma 1.4 の有限個の座標。使われ方：各次数の bar の余極限保存。 -/
lemma finitePower_preservesSequentialColimits (n : ℕ) :
    PreservesColimitsOfShape ℕ (coyoneda.obj (op (ULift.{u} (Fin n)))) := by
  letI : IsFinitelyPresentable.{u} (ULift.{u} (Fin n)) :=
    HasCardinalLT.isCardinalPresentable
      (hasCardinalLT_of_finite (ULift.{u} (Fin n)) Cardinal.aleph0 (by simp))
  have : PreservesFilteredColimitsOfSize.{0, 0}
      (coyoneda.obj (op (ULift.{u} (Fin n)))) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  infer_instance

/-- 概要：単体的モノイドの対角 bar の実関手。
方針：既存の実 bar 写像とその恒等・合成保存を束ねる。
規約：KST App. A。使われ方：実 rank 余極限の保存を関手として記述する。 -/
def monoidBarFunctor : SimplicialObject MonCat.{u} ⥤ SSet.{u} where
  obj := Comparison.monoidBar
  map := Comparison.monoidBarMap
  map_id := Comparison.monoidBarMap_id
  map_comp := Comparison.monoidBarMap_comp

end SerrePositivity.KST.ProExcision
