module

public import SerrePositivity.KST.LocalizingInvariants.DGQuotientNullCorner
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierPresentation
public import SerrePositivity.KST.SConstruction.DGKFixedInterface

/-!
概要：指定収縮付き商合成から、固定 dg 提示源内の実四角形を作る。
方針：始域の全対象商からの厳密延長を取り、同じ四つの辺を coherent nerve に写す。
規約：零角の ν 像の零性は別途認証し、自然な収縮の存在を仮定しない。
使われ方：K-S• の商零化と K-B の平坦懸垂屋根。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.LocalizingInvariants

variable (R : Type u) [CommRing R]
  {A B Q : PerfDGInput.{u, v} R} (i : A ⟶ B) (q : B ⟶ Q)
  (C : DGQuotient.ContractedFunctor R A Set.univ Q)
  (hC : C.toDGFunctor = i.down.comp q.down)

/-- 全対象商を元の固定 S の頂点として保持する。 -/
def dgFixedNullInput (A : PerfDGInput.{u, v} R) : PerfDGInput.{u, v} R := by
  letI : Small.{u} (dgNullCorner (D := A)) :=
    small_of_injective (DGQuotient.quotientObjectEquiv (D := A) Set.univ).symm.injective
  exact perfDGInputOf R (dgNullCorner (D := A))

/-- 元の始域から全対象商への、固定 S の厳密な左辺。 -/
def dgFixedNullLeft : A ⟶ dgFixedNullInput R A :=
  ULift.up (DGQuotient.inclusion R A Set.univ)

/-- 指定した同じ商合成の全対象商からの延長。 -/
def dgFixedNullTop : dgFixedNullInput R A ⟶ Q :=
  ULift.up (DGQuotient.extension R C)

include hC in
/-- 元の包含・商の合成と、零角経由の合成は固定 S の通常射として一致する。 -/
lemma dgFixedNull_comm :
    dgFixedNullLeft R (A := A) ≫ dgFixedNullTop R C = i ≫ q := by
  apply ULift.ext
  exact (DGQuotient.inclusion_comp_extension R C).trans hC

include hC in
/-- 元の四つの全一単体を保つ、固定 S 内の実零化四角形。 -/
lemma exists_dgFixedNullSquare :
    ∃ F : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶ dgKInputInfinity.{u, v} R,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge i).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ F =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := A))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ F =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullTop R C)).edge := by
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.exists_coherentSquare_of_comm i q
    (dgFixedNullLeft R (A := A)) (dgFixedNullTop R C) (dgFixedNull_comm R i q C hC).symm

include hC in
/-- 元の二射の Verdier 条件と零角の Perf 値の零性から、固定 ν の相対提示を得る。
実核・Verdier 条件の供給と零角の Perf 値の零性は、この構成の存在とは区別する。 -/
lemma exists_dgFixedNullRelativeDiagram
    (hV : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence (dgKInputNuMap R i) (dgKInputNuMap R q))
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R (dgFixedNullInput R A))) :
    ∃ t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, v} R),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge i).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ t.square = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ t.square =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := A))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ t.square =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullTop R C)).edge := by
  let d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{max (u + 1) v} := {
    left := dgKInputStableValue R A
    middle := dgKInputStableValue R B
    right := dgKInputStableValue R Q
    inclusion := dgKInputNuMap R i
    projection := dgKInputNuMap R q
    isVerdier := hV }
  have hi : SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge i).edge ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).edge := by
    rw [SSet.yonedaEquiv_symm_comp]
    exact congrArg (fun e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v} _⦋1⦌ =>
      SSet.yonedaEquiv.symm e) (dgKInputNu_edge R i)
  have hq : SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q).edge ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.projection).edge := by
    rw [SSet.yonedaEquiv_symm_comp]
    exact congrArg (fun e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v} _⦋1⦌ =>
      SSet.yonedaEquiv.symm e) (dgKInputNu_edge R q)
  obtain ⟨F, hb, hr, hl, ht⟩ := exists_dgFixedNullSquare R i q C hC
  have hFz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgFixedNullInput R A) := by
    have he := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target F
    let le : (dgKInputInfinity.{u, v} R).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgFixedNullInput R A)) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := A))
    have hle : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ F = SSet.yonedaEquiv.symm le.edge := hl
    rw [hle, Equiv.apply_symm_apply, le.tgt_eq] at he
    exact he.symm
  have hz' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (F ≫ dgKInputNu R) 0 1)) := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject ((dgKInputNu R).app _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 1)))
    rw [hFz]
    rw [dgKInputNu_vertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
    exact hz
  have hbi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).edge := by
    rw [← Category.assoc, hb, hi]
  have hqr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.projection).edge := by
    rw [← Category.assoc, hr, hq]
  exact ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.ofSquare (dgKInputNu R) d F hbi hqr hz', hb, hr, hl, ht⟩

include hC in
/-- 同じ相対提示の三頂点と商の全一単体を回収する。K-B の相対屋根の供給境界。 -/
lemma exists_dgFixedNullRelativeRoof
    (hV : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence (dgKInputNuMap R i) (dgKInputNuMap R q))
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R (dgFixedNullInput R A))) :
    ∃ t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, v} R),
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A ∧
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex B ∧
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Q ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge i).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ t.square = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q).edge := by
  obtain ⟨t, hb, hr, _, _⟩ := exists_dgFixedNullRelativeDiagram R i q C hC hV hz
  let ie : (dgKInputInfinity.{u, v} R).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex B) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge i
  let qe : (dgKInputInfinity.{u, v} R).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex B)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Q) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q
  have hbi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square = SSet.yonedaEquiv.symm ie.edge := hb
  have hqr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ t.square = SSet.yonedaEquiv.symm qe.edge := hr
  refine ⟨t, ?_, ?_, ?_, hb, hr⟩
  · have he := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source t.square
    rw [hbi, Equiv.apply_symm_apply, ie.src_eq] at he
    exact he.symm
  · have he := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target t.square
    rw [hbi, Equiv.apply_symm_apply, ie.tgt_eq] at he
    exact he.symm
  · have he := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target t.square
    rw [hqr, Equiv.apply_symm_apply, qe.tgt_eq] at he
    exact he.symm

end SerrePositivity.KST.LocalizingInvariants
