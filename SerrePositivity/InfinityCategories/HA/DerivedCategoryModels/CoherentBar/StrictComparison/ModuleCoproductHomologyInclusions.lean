module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ModuleCoproductHomology

/-!
概要：実加群直和ホモロジー同型の逆向きの各包含公式。
方針：同じ同型の順向きの包含公式に逆を合成する。
規約：実 summand 包含を保持する。
使われ方：層ホモロジー射の等号を各列で判定する。
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

@[reassoc]
lemma dgModuleCoproductHomologyIso_ι_inv (i : I) :
    Sigma.ι (fun j => ((moduleEvaluation R D x).obj (K j)).homology q) i ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgModuleCoproductHomologyIso R D K x q).inv =
    HomologicalComplex.homologyMap ((moduleEvaluation R D x).map (Sigma.ι K i)) q := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgModuleCoproductHomologyIso_ι R D K x q i, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
