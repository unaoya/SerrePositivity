module

public import SerrePositivity.KST.LocalizingInvariants.DGQuotientNullCorner
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierPresentation
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
      squareBottomEdge ≫ F = SSet.yonedaEquiv.symm (coherentNerveEdge i).edge ∧
      squareRightEdge ≫ F = SSet.yonedaEquiv.symm (coherentNerveEdge q).edge ∧
      squareLeftEdge ≫ F =
        SSet.yonedaEquiv.symm (coherentNerveEdge (dgFixedNullLeft R (A := A))).edge ∧
      squareTopEdge ≫ F =
        SSet.yonedaEquiv.symm (coherentNerveEdge (dgFixedNullTop R C)).edge := by
  exact RelativeVerdierDiagram.exists_coherentSquare_of_comm i q
    (dgFixedNullLeft R (A := A)) (dgFixedNullTop R C) (dgFixedNull_comm R i q C hC).symm

include hC in
/-- 元の二射の Verdier 条件と零角の Perf 値の零性から、固定 ν の相対提示を得る。
実核・Verdier 条件の供給と零角の Perf 値の零性は、この構成の存在とは区別する。 -/
lemma exists_dgFixedNullRelativeDiagram
    (hV : IsVerdierSequence (dgKInputNuMap R i) (dgKInputNuMap R q))
    (hz : IsZeroCategory (dgKInputStableValue R (dgFixedNullInput R A))) :
    ∃ t : RelativeVerdierDiagram (dgKInputNu.{u, v} R),
      squareBottomEdge ≫ t.square = SSet.yonedaEquiv.symm (coherentNerveEdge i).edge ∧
      squareRightEdge ≫ t.square = SSet.yonedaEquiv.symm (coherentNerveEdge q).edge ∧
      squareLeftEdge ≫ t.square =
        SSet.yonedaEquiv.symm (coherentNerveEdge (dgFixedNullLeft R (A := A))).edge ∧
      squareTopEdge ≫ t.square =
        SSet.yonedaEquiv.symm (coherentNerveEdge (dgFixedNullTop R C)).edge := by
  let d : VerdierSequence.{max (u + 1) v} := {
    left := dgKInputStableValue R A
    middle := dgKInputStableValue R B
    right := dgKInputStableValue R Q
    inclusion := dgKInputNuMap R i
    projection := dgKInputNuMap R q
    isVerdier := hV }
  have hi : SSet.yonedaEquiv.symm (coherentNerveEdge i).edge ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (stableArrow d.inclusion).edge := by
    rw [SSet.yonedaEquiv_symm_comp]
    exact congrArg (fun e : StableInfinity.{max (u + 1) v} _⦋1⦌ =>
      SSet.yonedaEquiv.symm e) (dgKInputNu_edge R i)
  have hq : SSet.yonedaEquiv.symm (coherentNerveEdge q).edge ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (stableArrow d.projection).edge := by
    rw [SSet.yonedaEquiv_symm_comp]
    exact congrArg (fun e : StableInfinity.{max (u + 1) v} _⦋1⦌ =>
      SSet.yonedaEquiv.symm e) (dgKInputNu_edge R q)
  obtain ⟨F, hb, hr, hl, ht⟩ := exists_dgFixedNullSquare R i q C hC
  have hFz : squareVertex F 0 1 = coherentNerveVertex (dgFixedNullInput R A) := by
    have he := squareLeftEdge_target F
    let le : (dgKInputInfinity.{u, v} R).Edge (coherentNerveVertex A)
        (coherentNerveVertex (dgFixedNullInput R A)) :=
      coherentNerveEdge (dgFixedNullLeft R (A := A))
    have hle : squareLeftEdge ≫ F = SSet.yonedaEquiv.symm le.edge := hl
    rw [hle, Equiv.apply_symm_apply, le.tgt_eq] at he
    exact he.symm
  have hz' : IsZeroCategory (stableObject (squareVertex (F ≫ dgKInputNu R) 0 1)) := by
    change IsZeroCategory (stableObject ((dgKInputNu R).app _ (squareVertex F 0 1)))
    rw [hFz]
    rw [dgKInputNu_vertex, _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableObject_vertex]
    exact hz
  have hbi : squareBottomEdge ≫ F ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (stableArrow d.inclusion).edge := by
    rw [← Category.assoc, hb, hi]
  have hqr : squareRightEdge ≫ F ≫ dgKInputNu R =
      SSet.yonedaEquiv.symm (stableArrow d.projection).edge := by
    rw [← Category.assoc, hr, hq]
  exact ⟨RelativeVerdierDiagram.ofSquare (dgKInputNu R) d F hbi hqr hz', hb, hr, hl, ht⟩

include hC in
/-- 同じ相対提示の三頂点と商の全一単体を回収する。K-B の相対屋根の供給境界。 -/
lemma exists_dgFixedNullRelativeRoof
    (hV : IsVerdierSequence (dgKInputNuMap R i) (dgKInputNuMap R q))
    (hz : IsZeroCategory (dgKInputStableValue R (dgFixedNullInput R A))) :
    ∃ t : RelativeVerdierDiagram (dgKInputNu.{u, v} R),
      squareVertex t.square 0 0 = coherentNerveVertex A ∧
      squareVertex t.square 1 0 = coherentNerveVertex B ∧
      squareVertex t.square 1 1 = coherentNerveVertex Q ∧
      squareBottomEdge ≫ t.square = SSet.yonedaEquiv.symm (coherentNerveEdge i).edge ∧
      squareRightEdge ≫ t.square = SSet.yonedaEquiv.symm (coherentNerveEdge q).edge := by
  obtain ⟨t, hb, hr, _, _⟩ := exists_dgFixedNullRelativeDiagram R i q C hC hV hz
  let ie : (dgKInputInfinity.{u, v} R).Edge (coherentNerveVertex A)
      (coherentNerveVertex B) := coherentNerveEdge i
  let qe : (dgKInputInfinity.{u, v} R).Edge (coherentNerveVertex B)
      (coherentNerveVertex Q) := coherentNerveEdge q
  have hbi : squareBottomEdge ≫ t.square = SSet.yonedaEquiv.symm ie.edge := hb
  have hqr : squareRightEdge ≫ t.square = SSet.yonedaEquiv.symm qe.edge := hr
  refine ⟨t, ?_, ?_, ?_, hb, hr⟩
  · have he := squareBottomEdge_source t.square
    rw [hbi, Equiv.apply_symm_apply, ie.src_eq] at he
    exact he.symm
  · have he := squareBottomEdge_target t.square
    rw [hbi, Equiv.apply_symm_apply, ie.tgt_eq] at he
    exact he.symm
  · have he := squareRightEdge_target t.square
    rw [hqr, Equiv.apply_symm_apply, qe.tgt_eq] at he
    exact he.symm

end SerrePositivity.KST.LocalizingInvariants
