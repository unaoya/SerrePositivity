module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.RoofPastingAttachment
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierTwoArrowQuotientPasting

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
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q}
  (D L : (Δ[1] : SSet.{u}) ⟶ B.obj)
  {F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj} (s : SquareCosliceSeed F)
  (r : VerdierCosliceFractionNormalization h (fractionSquarePoint F) (twoArrowCosliceEdge s)
    ((coprod.desc D L).app (Opposite.op ⦋0⦌) twoArrowFirstTarget)
    ((coprod.desc D L).app (Opposite.op ⦋0⦌) twoArrowSecondTarget))

/-- 元の商四角形と同じ分数三角形を貼った五頂点の全 coslice 図式。 -/
def verdierRoofPastingCoslice : (pastingCorner : SSet.{u}).op ⟶
    sliceUnder (fractionSquarePoint F) :=
  roofPastingCosliceDiagram s.lift (twoArrowLiftedFractionTriangle D L s r)
    (twoArrowLiftedFractionTriangle_last D L s r)

lemma verdierRoofPastingCoslice_original : roofPastingOriginalPair ≫
    verdierRoofPastingCoslice D L s r = twoArrowCosliceDiagram s := by
  apply coprod.hom_ext
  · simp only [← Category.assoc, roofPastingOriginalPair, coprod.inl_desc,
      twoArrowCosliceDiagram, twoArrowSquareBoundary]
    simp only [Category.assoc]
    rw [verdierRoofPastingCoslice, roofPastingCosliceDiagram_square]
    rw [← Category.assoc]
    apply congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] => f ≫ s.lift)
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  · simp only [← Category.assoc, roofPastingOriginalPair, coprod.inr_desc,
      twoArrowCosliceDiagram, twoArrowSquareBoundary]
    simp only [Category.assoc]
    rw [verdierRoofPastingCoslice, roofPastingCosliceDiagram_square]
    rw [← Category.assoc]
    apply congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] => f ≫ s.lift)
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide

lemma verdierRoofPastingCoslice_fraction : roofPastingFractionSpan ≫
    verdierRoofPastingCoslice D L s r = r.spanLift := by
  apply horn₂₀.isPushout.hom_ext
  · simp only [← Category.assoc, roofPastingFractionSpan, horn₂₀.isPushout.inl_desc,
      VerdierCosliceFractionNormalization.spanLift]
    simp only [Category.assoc]
    rw [verdierRoofPastingCoslice, roofPastingCosliceDiagram_triangle,
      twoArrowLiftedFractionTriangle, stdSimplex.δ_comp_yonedaEquiv_symm]
    have he : (sliceUnder (fractionSquarePoint F)).δ (2 : Fin 3) r.lift.triangle.simplex =
        r.lift.first.edge := r.lift.triangle.d₂
    exact congrArg SSet.yonedaEquiv.symm he
  · simp only [← Category.assoc, roofPastingFractionSpan, horn₂₀.isPushout.inr_desc,
      VerdierCosliceFractionNormalization.spanLift]
    simp only [Category.assoc]
    rw [verdierRoofPastingCoslice, roofPastingCosliceDiagram_triangle,
      twoArrowLiftedFractionTriangle, stdSimplex.δ_comp_yonedaEquiv_symm]
    have he : (sliceUnder (fractionSquarePoint F)).δ (1 : Fin 3) r.lift.triangle.simplex =
        r.lift.diagonal.edge := r.lift.triangle.d₁
    exact congrArg SSet.yonedaEquiv.symm he

/-- 添付後の同じ全 coslice 図式は、五頂点図式の同じ全写像による制限そのもの。 -/
lemma verdierRoofPastingCoslice_attachment : roofPastingAttachmentMap ≫
    verdierRoofPastingCoslice D L s r =
      cosliceSpanLiftDiagram (coprod.desc D L) (twoArrowCosliceDiagram s)
        twoArrowFirstTarget twoArrowSecondTarget r := by
  apply pushout.hom_ext
  · rw [← Category.assoc, roofPastingAttachmentMap_original,
      verdierRoofPastingCoslice_original, cosliceSpanLiftDiagram_original]
  · rw [← Category.assoc, roofPastingAttachmentMap_fraction,
      verdierRoofPastingCoslice_fraction, cosliceSpanLiftDiagram, pushout.inr_desc]

variable (hb : squareBottomEdge ≫ F = D ≫ q.hom) (ht : squareTopEdge ≫ F = L ≫ q.hom)

/-- 元の全商錐も、同じ五頂点の全錐の厳密制限そのもの。 -/
lemma verdierRoofPastingCone_attachment : joinMap (𝟙 (Δ[0] : SSet.{u}))
    roofPastingAttachmentMap ≫
      (roofPastingCone s.lift (twoArrowLiftedFractionTriangle D L s r)
        (twoArrowLiftedFractionTriangle_last D L s r)).val =
      (cosliceSpanQuotientCone (coprod.desc D L) (twoArrowCosliceDiagram s)
        twoArrowFirstTarget twoArrowSecondTarget r
        (twoArrowCoslice_projection q.hom D L F s hb ht)).val := by
  change joinMap (𝟙 (Δ[0] : SSet.{u})) roofPastingAttachmentMap ≫
    sliceUnderUncurry (verdierRoofPastingCoslice D L s r) = sliceUnderUncurry _
  rw [← sliceUnderUncurry_precomp, verdierRoofPastingCoslice_attachment]

/-- 同じ元の商錐から読む分母四角形は、指定合成三角柱の分母面そのもの。 -/
lemma verdierRoofPasting_denominator : twoArrowDenominatorSquare
    (cosliceSpanQuotientCone (coprod.desc D L) (twoArrowCosliceDiagram s)
      twoArrowFirstTarget twoArrowSecondTarget r
      (twoArrowCoslice_projection q.hom D L F s hb ht)) =
    pastingSquare (verdierTwoArrowQuotientPasting D L s r) 2 := by
  rw [twoArrowDenominatorSquare, conePairSquare,
    ← verdierRoofPastingCone_attachment D L s r hb ht]
  rw [← Category.assoc (joinMap _ _) (joinMap _ _), ← joinMap_comp,
    Category.id_comp, roofPastingAttachmentMap_denominator]
  exact (roofPastingPrism_denominator s.lift (twoArrowLiftedFractionTriangle D L s r)
    (twoArrowLiftedFractionTriangle_last D L s r)).symm

/-- 同じ元の商錐から読む分子四角形は、指定合成三角柱の分子面そのもの。 -/
lemma verdierRoofPasting_numerator : (β_ Δ[1] Δ[1]).hom ≫ twoArrowNumeratorSquare
    (cosliceSpanQuotientCone (coprod.desc D L) (twoArrowCosliceDiagram s)
      twoArrowFirstTarget twoArrowSecondTarget r
      (twoArrowCoslice_projection q.hom D L F s hb ht)) =
    pastingSquare (verdierTwoArrowQuotientPasting D L s r) 1 := by
  rw [twoArrowNumeratorSquare, conePairSquare,
    ← verdierRoofPastingCone_attachment D L s r hb ht]
  rw [← Category.assoc (joinMap _ _) (joinMap _ _), ← joinMap_comp,
    Category.id_comp, roofPastingAttachmentMap_numerator]
  exact (roofPastingPrism_numerator s.lift (twoArrowLiftedFractionTriangle D L s r)
    (twoArrowLiftedFractionTriangle_last D L s r)).symm

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPastingCone_attachment := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierRoofPastingCone_attachment

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierRoofPastingCoslice (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPastingCoslice := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierRoofPastingCoslice

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPastingCoslice_attachment := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierRoofPastingCoslice_attachment

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPastingCoslice_fraction := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierRoofPastingCoslice_fraction

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPastingCoslice_original := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierRoofPastingCoslice_original

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPasting_denominator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierRoofPasting_denominator

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPasting_numerator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierRoofPasting_numerator

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPastingCoslice._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierRoofPastingCoslice._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRoofPastingCoslice.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierRoofPastingCoslice.eq_1
