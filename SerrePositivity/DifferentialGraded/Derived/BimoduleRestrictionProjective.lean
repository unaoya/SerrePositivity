module
public import SerrePositivity.DifferentialGraded.Derived.RestrictionProjective
public import SerrePositivity.DifferentialGraded.Bimodule.Right


/-!
概要：積 dg 圏の生成 sphere の右制限から固定 bimodule 解像度の射影性を回収する。
方針：同じ実制限同型と semifree filtration の Hom tower を使う。
規約：元の解像度を別の右射影的解像度へ取り替えない。
使われ方：cell source 上の二つの固定 graph 解像度。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

lemma BimoduleSemifreeResolution.right_homotopicallyProjective_of_cells
    {M : BimoduleCategory A B C} (P : BimoduleSemifreeResolution A B C M)
    (hcell : ∀ (c : C) (x : (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) (n : ℤ),
      moduleHomotopicallyProjective A B
        ((tensorRightRestriction A B C c).obj
          (freeSphere A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ x n))) (c : C) :
    moduleHomotopicallyProjective A B ((BimoduleCategory.evaluation A B C c).obj P.obj) := by
  exact moduleHomotopicallyProjective_of_iso A B
    (rightModuleBimoduleRightRestrictionIso A B C P.source c).symm
    (moduleSemifree_restriction_homotopicallyProjective A B
      (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (tensorRightRestrictionInclusion A B C c)
      (hcell c) P.semifree)

end SerrePositivity.DifferentialGraded
