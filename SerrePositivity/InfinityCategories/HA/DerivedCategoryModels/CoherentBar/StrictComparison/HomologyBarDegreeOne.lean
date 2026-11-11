module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarTopExact

/-!
概要：ホモロジー bar の一次微分は、図式の射による余極限の関係式である。
方針：元の一単体の二つの面を、その始点と終点へ戻す。
規約：通常のホモロジー図式 F を扱う。
使われ方：零次ホモロジーと colim F の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits Opposite SSet AlgebraicTopology
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [PartialOrder J]
  (F : J ⥤ ModuleCat.{u} R)

def dgHomologyBarVertex (j : J) : F.obj j ⟶ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R F).X 0 :=
  Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarFamily R F (op ⦋0⦌)) (nerveEquiv.symm j)

lemma dgHomologyBarEdge_face_zero {j k : J} (f : j ⟶ k) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarFamily R F (op ⦋1⦌)) (CategoryTheory.nerve.edgeMk f).edge ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F).δ 0 = F.map f ≫ dgHomologyBarVertex R F k := by
  erw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarMap_ι]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarCoefficient_transport R F (CategoryTheory.nerve.edgeMk f).tgt_eq _ f

lemma dgHomologyBarEdge_face_one {j k : J} (f : j ⟶ k) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarFamily R F (op ⦋1⦌)) (CategoryTheory.nerve.edgeMk f).edge ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F).δ 1 = dgHomologyBarVertex R F j := by
  erw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarMap_ι]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarTransport_ι R F (Δ := op ⦋0⦌)
    (CategoryTheory.nerve.edgeMk f).src_eq.symm _

lemma dgHomologyBarDifferential_one :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R F).d 1 0 =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F).δ 0 - (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F).δ 1 := by
  rw [AlternatingFaceMapComplex.obj_d_eq]
  erw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one,
    pow_zero, one_smul, pow_one, neg_smul, sub_eq_add_neg]

lemma dgHomologyBarEdge_d {j k : J} (f : j ⟶ k) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarFamily R F (op ⦋1⦌)) (CategoryTheory.nerve.edgeMk f).edge ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R F).d 1 0 =
        F.map f ≫ dgHomologyBarVertex R F k - dgHomologyBarVertex R F j := by
  rw [dgHomologyBarDifferential_one, Preadditive.comp_sub,
    dgHomologyBarEdge_face_zero, dgHomologyBarEdge_face_one]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
