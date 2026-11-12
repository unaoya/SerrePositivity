module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexCoproductHomologyInclusions
public import SerrePositivity.DifferentialGraded.Module.ActionLimits

/-!
概要：実 dg 加群直和の評価ホモロジーと成分ホモロジーの直和の自然な同型。
方針：評価の直和保存と複体直和のホモロジー比較を合成する。
規約：実包含射に対する可換性を含める。
使われ方：coherent bar の各層のホモロジー係数。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : Type u} (K : I → ModuleCategory R D) (x : D) (q : ℤ)

def dgModuleCoproductHomologyIso :
    ((moduleEvaluation R D x).obj (∐ K)).homology q ≅
      ∐ fun i => ((moduleEvaluation R D x).obj (K i)).homology q :=
  HomologicalComplex.homologyMapIso (PreservesCoproduct.iso (moduleEvaluation R D x) K) q ≪≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCoproductHomologyIso R (fun i => (moduleEvaluation R D x).obj (K i)) q

@[reassoc]
lemma dgModuleCoproductHomologyIso_ι (i : I) :
    HomologicalComplex.homologyMap ((moduleEvaluation R D x).map (Sigma.ι K i)) q ≫
      (dgModuleCoproductHomologyIso R D K x q).hom =
    Sigma.ι (fun j => ((moduleEvaluation R D x).obj (K j)).homology q) i := by
  have h := (isColimitOfHasCoproductOfPreservesColimit
    (moduleEvaluation R D x) K).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (Discrete.functor (fun i => (moduleEvaluation R D x).obj (K i))))
        (Discrete.mk i)
  simp only [dgModuleCoproductHomologyIso, Iso.trans_hom,
    HomologicalComplex.homologyMapIso_hom]
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp]
  erw [h]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCoproductHomologyIso_ι R _ i q

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
