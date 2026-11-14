module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientExactDescent
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.ExactFunctorCategoryEquivalence
/-!
概要：Drinfeld 商の完全関手 ∞ 圏を、元の零化完全関手 ∞ 圏と同定する。
方針：全関手圏の局所化の充満忠実性と、完全性を反映する実辺表示を使う。
規約：全自然変換を保持。使われ方：安定 Verdier 列の普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalClosed SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
/-- 商の前合成は、反転関手への因子化を忘れた元の全関手圏でも充満忠実。 -/
lemma dgQuotientPrecomposition_isFullyFaithful (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (Y : SSet.{max u v}) [Quasicategory Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)).app Y) := by
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierLocalizationPrecomposition_isFullyFaithful A D P hP Y
  have hi := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).obj Y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) Y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) Y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)).ι at hi
  have hh := hf.comp hi
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι] at hh
  exact hh
/-- 零化完全関手圏への、実商射影による前合成。 -/
def dgVerdierExactPrecomposition (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (Y : SSet.{max u v}) : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactFunctors (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P) Y : SSet.{max u v}) ⟶
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactFunctors (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) Y (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P) : SSet.{max u v}) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_isExactFunctor A D P hP
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactPrecomposition (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P)
    (by rintro _ ⟨x, hx, rfl⟩; exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_kills A D P ⟨x, hx⟩) Y
/-- 任意の安定標的について、商の全完全関手圏は元の全零化完全関手圏と同値。 -/
lemma dgVerdierExactPrecomposition_isQCatEquivalence (P : Set D)
    (hP : DGQuotient.localKFlat A D P) (Y : SSet.{max u v}) [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgVerdierExactPrecomposition A D P hP Y) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_isExactFunctor A D P hP
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactPrecomposition_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P)
    (by rintro _ ⟨x, hx, rfl⟩; exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_kills A D P ⟨x, hx⟩)
  · exact dgQuotientPrecomposition_isFullyFaithful A D P hP Y
  · intro F hF hkill
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierExactFunctor_extension_exists A D P hP F
      (fun b => hkill _ ⟨b.val, b.property, rfl⟩)
end SerrePositivity.InfinityCategories.Project.DerivedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite AGH "Prop A.1.5–A.1.7" (partial := special) "仮定：Lean が強い。局所 K 平坦な dg 商と安定な標的。結論：同じ商への完全関手の前合成は、指定部分圏で零となる完全関手の準圏との同値（A.1.5 の普遍性の dg 版）。"] _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierExactPrecomposition_isQCatEquivalence
