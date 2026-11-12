module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitConePointSection
public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitNativeConeComparison
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentConeSourceWeightedRestriction

/-!
概要：構成した coherent 錐全体の Hom の族の制限は、元の反転 end の点の比較族に一致。
方針：元の錐の weighted な切断表示を代入し、零単体の射の全次数での定数評価を照合する。
規約：比較の始域・終域だけでなく元の射そのものを同定する。使われ方：native な極限判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance coneSourceRestrictionSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I]

/-- 元の coherent 錐全体の全 Hom 比較族の制限は、元の反転 end の点の比較族そのもの。 -/
lemma homotopyLimitCoherentConeSourceFamily_restrict
    (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceFamily (homotopyLimitCoherentCone D) (homotopyLimit D)
        (homotopyLimitCoherentCone_vertex D) X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction (homotopyLimitCoherentCone D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) =
        homotopyLimitNativeConeComparison D X := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D)
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceFamily_restriction_weighted D _ _ _
    (homotopyLimitConeWeightedPointSection D)
    (homotopyLimitCoherentCone_cosliceSection_weighted D)]
  rw [homotopyLimitNativeConeComparison_uncurry]
  simp only [← Category.assoc]
  congr 1
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, s⟩
  change (ULift.up
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D) ⋙ SSet.opFunctor)).app
          (Opposite.op ⦋n⦌)
          (((inv (fst _ (Δ[0] : SSet.{u + 1}))).app
            (Opposite.op ⦋n⦌) σ).1.down, ((homotopyLimitLiftedEndPoint D).app (Opposite.op ⦋n⦌)
            ((inv (fst _ (Δ[0] : SSet.{u + 1}))).app (Opposite.op ⦋n⦌) σ).2).down)), s) =
    (ULift.up
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D) ⋙ SSet.opFunctor)).app
          (Opposite.op ⦋n⦌)
          (σ.down, (homotopyLimitReflectedEndPointMap D).app (Opposite.op ⦋n⦌) PUnit.unit)), s)
  have hf := ConcreteCategory.congr_hom
    (NatTrans.congr_app (IsIso.inv_hom_id
      (fst ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I))
        (Δ[0] : SSet.{u + 1}))) (Opposite.op ⦋n⦌)) σ
  change ((inv (fst _ (Δ[0] : SSet.{u + 1}))).app (Opposite.op ⦋n⦌) σ).1 = σ at hf
  rw [hf]
  congr 3
  simp only [homotopyLimitLiftedEndPoint, SSet.yonedaEquiv_symm_zero]
  congr 1

end SerrePositivity.KST.Spectra.OmegaSpectrum
