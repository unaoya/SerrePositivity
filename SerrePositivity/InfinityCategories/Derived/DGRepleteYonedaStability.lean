module
public import SerrePositivity.InfinityCategories.Derived.DGRepleteYonedaEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGNerveUniverseLift
public import SerrePositivity.InfinityCategories.F1.UniverseInnerFibration
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Stable.EquivalenceStability

/-! # 共通宇宙の前三角 dg nerve の安定性

概要：前三角 dg 圏の対象宇宙を上げた nerve と元の nerve の ULift は安定。
方針：ホモトピー表現可能部分との実同値で安定性を輸送し、実宇宙同型と合成する。
規約：元の小さい宇宙への降下は別工程。使われ方：β3 の前三角性からの安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の nerve の ULift とホモトピー表現可能部分の明示的 ∞ 圏同値。 -/
def dgRepleteYonedaULiftEquivalence :
    QCatEquivalence
      ((SSet.uliftFunctor.{max (u + 1) v, max u v}).obj (dgNerve A D))
      (dgHomotopyRepresentableNerve A D) :=
  (qCatEquivalenceOfIso (dgNerveUniverseLiftIso.{u, v, max (u + 1) v} A D)).trans
    (dgRepleteYonedaNerveEquivalence A D)

/-- 前三角 dg 圏の対象宇宙を上げた nerve は安定。 -/
lemma dgUniverseLiftNerve_isStable [IsDGPretriangulated A D] :
    IsStable (dgNerve A (DGUniverseLift.{v, max (u + 1) v} D)) :=
  (dgRepleteYonedaNerveEquivalence A D).isStable_iff.mpr inferInstance

/-- 前三角 dg 圏の元の nerve を単体集合として ULift すると安定。 -/
lemma dgNerveULift_isStable_of_pretriangulated [IsDGPretriangulated A D] :
    IsStable ((SSet.uliftFunctor.{max (u + 1) v, max u v}).obj (dgNerve A D)) :=
  (dgRepleteYonedaULiftEquivalence A D).isStable_iff.mpr inferInstance

/-- ホモトピー表現可能部分への実 Yoneda の nerve は完全。 -/
lemma dgRepleteYonedaNerve_isExactFunctor :
    IsExactFunctor (dgNerve.map (dgRepleteYoneda A D)) :=
  isExactFunctor_of_isQCatEquivalence
    (dgRepleteYonedaNerveEquivalence A D).isQCatEquivalence

/-- 選択された同値の逆写像も完全。 -/
lemma dgRepleteYonedaNerveInverse_isExactFunctor :
    IsExactFunctor (dgRepleteYonedaNerveEquivalence A D).inv :=
  isExactFunctor_of_isQCatEquivalence
    (dgRepleteYonedaNerveEquivalence A D).symm.isQCatEquivalence

end SerrePositivity.InfinityCategories
