module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.RoofPastingAttachment
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierTwoArrowQuotientPasting

/-!
概要：実右分数添付の同じ商全錐を、元の指定合成三角柱の五頂点図式へ厳密接続する。
方針：二辺と分数 span の各制限を保ち、同じ pushout 写像を coslice で比較する。
規約：全 coslice 図式と全錐は射の等式で保持し、新しい整合仮定を要求しない。
使われ方：実屋根の全商比較を、元の商四角形を含む合成二胞体へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q}
  (D L : (Δ[1] : SSet.{u}) ⟶ B.obj)
  {F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj} (s : _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed F)
  (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization h (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint F) (twoArrowCosliceEdge s)
    ((coprod.desc D L).app (Opposite.op ⦋0⦌) twoArrowFirstTarget)
    ((coprod.desc D L).app (Opposite.op ⦋0⦌) twoArrowSecondTarget))

/-- 元の商四角形と同じ分数三角形を貼った五頂点の全 coslice 図式。 -/
def verdierRoofPastingCoslice : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}).op ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint F) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.roofPastingCosliceDiagram s.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle D L s r)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle_last D L s r)

lemma verdierRoofPastingCoslice_original : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.roofPastingOriginalPair ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice D L s r = twoArrowCosliceDiagram s := by
  apply coprod.hom_ext
  · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.roofPastingOriginalPair, coprod.inl_desc,
      twoArrowCosliceDiagram, twoArrowSquareBoundary]
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice, roofPastingCosliceDiagram_square]
    rw [← Category.assoc]
    apply congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] => f ≫ s.lift)
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.roofPastingOriginalPair, coprod.inr_desc,
      twoArrowCosliceDiagram, twoArrowSquareBoundary]
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice, roofPastingCosliceDiagram_square]
    rw [← Category.assoc]
    apply congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] => f ≫ s.lift)
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide

lemma verdierRoofPastingCoslice_fraction : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.roofPastingFractionSpan ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice D L s r = r.spanLift := by
  apply horn₂₀.isPushout.hom_ext
  · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.roofPastingFractionSpan, horn₂₀.isPushout.inl_desc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization.spanLift]
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice, roofPastingCosliceDiagram_triangle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle, stdSimplex.δ_comp_yonedaEquiv_symm]
    have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint F)).δ (2 : Fin 3) r.lift.triangle.simplex =
        r.lift.first.edge := r.lift.triangle.d₂
    exact congrArg SSet.yonedaEquiv.symm he
  · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.roofPastingFractionSpan, horn₂₀.isPushout.inr_desc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization.spanLift]
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice, roofPastingCosliceDiagram_triangle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle, stdSimplex.δ_comp_yonedaEquiv_symm]
    have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint F)).δ (1 : Fin 3) r.lift.triangle.simplex =
        r.lift.diagonal.edge := r.lift.triangle.d₁
    exact congrArg SSet.yonedaEquiv.symm he

/-- 添付後の同じ全 coslice 図式は、五頂点図式の同じ全写像による制限そのもの。 -/
lemma verdierRoofPastingCoslice_attachment : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.roofPastingAttachmentMap ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice D L s r =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanLiftDiagram (coprod.desc D L) (twoArrowCosliceDiagram s)
        twoArrowFirstTarget twoArrowSecondTarget r := by
  apply pushout.hom_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.roofPastingAttachmentMap_original,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice_original, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanLiftDiagram_original]
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.roofPastingAttachmentMap_fraction,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice_fraction, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanLiftDiagram, pushout.inr_desc]

variable (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F = D ≫ q.hom) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ F = L ≫ q.hom)

/-- 元の全商錐も、同じ五頂点の全錐の厳密制限そのもの。 -/
lemma verdierRoofPastingCone_attachment : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u}))
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.roofPastingAttachmentMap ≫
      (roofPastingCone s.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle D L s r)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle_last D L s r)).val =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanQuotientCone (coprod.desc D L) (twoArrowCosliceDiagram s)
        twoArrowFirstTarget twoArrowSecondTarget r
        (twoArrowCoslice_projection q.hom D L F s hb ht)).val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.roofPastingAttachmentMap ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice D L s r) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice_attachment]

/-- 同じ元の商錐から読む分母四角形は、指定合成三角柱の分母面そのもの。 -/
lemma verdierRoofPasting_denominator : twoArrowDenominatorSquare
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanQuotientCone (coprod.desc D L) (twoArrowCosliceDiagram s)
      twoArrowFirstTarget twoArrowSecondTarget r
      (twoArrowCoslice_projection q.hom D L F s hb ht)) =
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierTwoArrowQuotientPasting D L s r) 2 := by
  rw [twoArrowDenominatorSquare, conePairSquare,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCone_attachment D L s r hb ht]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _), ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    Category.id_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.roofPastingAttachmentMap_denominator]
  exact (roofPastingPrism_denominator s.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle D L s r)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle_last D L s r)).symm

/-- 同じ元の商錐から読む分子四角形は、指定合成三角柱の分子面そのもの。 -/
lemma verdierRoofPasting_numerator : (β_ Δ[1] Δ[1]).hom ≫ twoArrowNumeratorSquare
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanQuotientCone (coprod.desc D L) (twoArrowCosliceDiagram s)
      twoArrowFirstTarget twoArrowSecondTarget r
      (twoArrowCoslice_projection q.hom D L F s hb ht)) =
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierTwoArrowQuotientPasting D L s r) 1 := by
  rw [twoArrowNumeratorSquare, conePairSquare,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCone_attachment D L s r hb ht]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _), ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    Category.id_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.roofPastingAttachmentMap_numerator]
  exact (roofPastingPrism_numerator s.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle D L s r)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.twoArrowLiftedFractionTriangle_last D L s r)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPastingCone_attachment := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCone_attachment

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPastingCoslice := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPastingCoslice_attachment := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice_attachment

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPastingCoslice_fraction := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice_fraction

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPastingCoslice_original := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice_original

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPasting_denominator := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPasting_denominator

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPasting_numerator := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPasting_numerator

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPastingCoslice._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPastingCoslice.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRoofPastingCoslice.eq_1
