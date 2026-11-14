module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGFunctorQuasiIsoFullyFaithful
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGVertexIsoOfH0
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence

/-! # 任意の dg 準同値の実 ∞ 圏同値

概要：全射性を要求しない dg 準同値は、native dg nerve の ∞ 圏同値を誘導する。
方針：実写像空間の充満忠実性と H⁰ の本質的全射から得た実頂点同型を合わせる。
規約：前三角性も不要。使われ方：β3 の平坦模型と β5 の dg 模型比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories
open _root_.CategoryTheory _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]

/-- dg 関手の H⁰ が本質的全射なら、実 nerve の対象も実同型まで覆う。 -/
lemma dgNerve_map_isEssentiallySurjective (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    (he : F.onHomotopy.EssSurj) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) := by
  let := he
  intro y
  obtain ⟨y, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
  let Y := (_root_.SerrePositivity.DifferentialGraded.toHomotopy A E).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
  let X := F.onHomotopy.objPreimage Y
  let x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) X.as
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexIsoOfH0 A E (F.onHomotopy.objObjPreimageIso Y)⟩

/-- 一般の dg 準同値の native nerve は ∞ 圏同値である。 -/
theorem dgNerve_map_isQCatEquivalence_of_quasiEquivalence (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    (h : QuasiEquivalence F) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.qCatEquivalenceOfFullyFaithfulEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isFullyFaithful_of_quasiIso F h.1)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.dgNerve_map_isEssentiallySurjective F h.2)).isQCatEquivalence

/-- dg 準同値から明示的な ∞ 圏同値を選ぶ。 -/
def dgQuasiEquivalenceNerveEquivalence (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) (h : _root_.SerrePositivity.DifferentialGraded.QuasiEquivalence F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.dgNerve_map_isQCatEquivalence_of_quasiEquivalence F h).choose

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.1.20" (partial := component) "仮定：可換環上の dg 準同値 F（HA の弱同値保存の部分と一致）。結論：dgNerve.map F は準圏の同値。右随伴の構成およびファイブレーション保存は含まず、dg 圏のモデル構造と Joyal の ModelCategory SSet の instance なし（Lean が弱い）。"] _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.dgNerve_map_isQCatEquivalence_of_quasiEquivalence
