module

public import SerrePositivity.InfinityCategories.F2.Compact.ColimitRepresentableCone
public import SerrePositivity.InfinityCategories.F1.CoherentSpaceSmallLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.SiftedColimitPreservation

/-!
概要：元の全共変 Hom の錐によって、指定された全余錐の余極限性を双方向に判定する。
方針：同じ元の図式の各評価の小極限を構成し、全関手圏の極限を元の極限へ反映する。
規約：元の全錐・余錐と同じ全関手を保持し、頂点の同値だけで代用しない。
使われ方：元の P_Σ 左 Kan 延長の sifted 保存性を全 Hom 比較へ還元する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F2.Compact

/-- 元の反対図式の全共変 Hom 錐の極限性は、元の同じ全錐の極限性を反映する。 -/
lemma covariantRepresentableDiagram_reflects_isLimit
    {K C : SSet.{u}} [Quasicategory C] {D : K ⟶ C.op}
    (c : JoinCone D) (hc : IsLimitCone (mapJoinCone (covariantRepresentableDiagram C)
      (JoinCone.ulift.{u, u + 1} c))) : IsLimitCone c := by
  have hp : HasPointwiseLimits ((SSet.uliftFunctor.{u + 1, u}).map D ≫
      covariantRepresentableDiagram C) := by
    intro y
    exact hasLimit_coherentSpaceDiagram _
  have hpoint : IsPointwiseLimitCone (mapJoinCone (covariantRepresentableDiagram C)
      (JoinCone.ulift.{u, u + 1} c)) :=
    isPointwiseLimitCone_of_isLimitCone_of_hasPointwiseLimits hp
      (mapJoinCone (covariantRepresentableDiagram C) (JoinCone.ulift.{u, u + 1} c)) hc
  apply isLimitCone_of_covariantRepresentableInfinity (C := C.op) c
  intro x
  let y : C _⦋0⦌ := SSet.opObjEquiv x
  have hx := hpoint (ULift.up y)
  change IsLimitCone (mapJoinCone
    (covariantRepresentableDiagram C ≫ evaluateFunctorAt (ULift.up y))
      (JoinCone.ulift.{u, u + 1} c)) at hx
  rw [covariantRepresentableDiagram_evaluation, ← homInfinityCovariant_eq_yonedaEvaluation] at hx
  have h : IsLimitCone (mapJoinCone
      (covariantRepresentableInfinity (C := C.op) (SSet.opObjEquiv.symm y))
      (JoinCone.ulift.{u, u + 1} c)) := hx.of_functorIso (FunctorIso.precomp
    (homInfinityCovariant_covariantIso (C := C.op) (SSet.opObjEquiv.symm y))
    (JoinCone.ulift.{u, u + 1} c).val)
  have he : SSet.opObjEquiv.symm y = x := Equiv.symm_apply_apply _ x
  rwa [he] at h

/-- 元の指定全余錐が余極限であることと、その元の全 Hom 錐が極限であることは同値。 -/
lemma isColimitCone_iff_fullHomCone {K C : SSet.{u}} [Quasicategory C] {D : K ⟶ C}
    (c : JoinCocone D) : IsColimitCone c ↔ IsLimitCone (colimitRepresentableCone c) :=
  ⟨colimitRepresentableCone_isLimit c, fun hc =>
    (F1B.kanIsColimitCone_iff_reverseCone c).mpr
      (covariantRepresentableDiagram_reflects_isLimit (F1B.kanCoconeReverseCone c) hc)⟩

/-- 元の関手の sifted 保存性は、元の全余錐像の全 Hom 錐の極限性と同値。 -/
lemma preservesSmallSiftedColimits_iff_fullHomCones
    {X Y : SSet.{u + 1}} [Quasicategory Y] (G : X ⟶ Y) :
    PreservesSmallSiftedColimits G ↔
      ∀ (I : SSet.{u}) [IsSiftedInfinity I]
        (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ X) (c : JoinCocone D),
        IsColimitCone c → IsLimitCone (colimitRepresentableCone (mapJoinCocone G c)) := by
  constructor
  · intro h I hI D c hc
    exact (isColimitCone_iff_fullHomCone _).mp (h I D c hc)
  · intro h I hI D c hc
    exact (isColimitCone_iff_fullHomCone _).mpr (h I D c hc)

end SerrePositivity.InfinityCategories.HomotopyLimits
