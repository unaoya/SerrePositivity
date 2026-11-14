module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSourceCodeCoproduct
public import SerrePositivity.DifferentialGraded.Presentation.Category
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence
/-!
概要：再添字済み共通提示の各成分で、元の dg 評価関手を厳密に回収する。
方針：逆再添字と評価の恒等式、および非連結和の成分上の厳密式を合成する。
規約：対象だけの等式や閉零自然同型に弱めない。
使われ方：c′ の異なる出発提示をまとめた際の seed 精密化の因子分解。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) {J : Type u}
  (c : J → DGCategoryPresentationCode R κ)

lemma dgKappaSourceCodeCoproductInclusion_comp_desc
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaFreeSumShape (fun j => (c j).ordinal)) (D : Type v) [DGCategory R D]
    (F : ∀ j, DGFunctor R ((c j).Objects R κ) D) (j : J) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSourceCodeCoproductInclusion R κ c s j).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSourceCodeCoproductDesc R κ c s D F) = F j := by
  letI := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSourceCodeSigmaData R κ c).enrichment R κ.ord.ToType _
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSourceCodeCoproductInclusion _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSourceCodeCoproductDesc
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSourceCodeCoproductEvaluation
  rw [strictDGFunctor_comp_assoc, ← strictDGFunctor_comp_assoc
    (DGCategoryPresentationData.reindexInverse R κ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSourceCodeSigmaData R κ c)
      s.ordinal s.reindex),
    DGCategoryPresentationData.reindexInverse_comp_evaluation, strictDGFunctor_id_comp]
  exact DGCategoryPresentationData.sigmaInclusion_comp_sigmaDesc R κ.ord.ToType J
    (fun j => (c j).Objects R κ) (fun j => (c j).toData R κ) D F j

end SerrePositivity.InfinityCategories.Project.DerivedCategories
