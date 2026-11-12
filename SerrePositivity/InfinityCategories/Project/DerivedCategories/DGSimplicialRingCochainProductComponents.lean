module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplicialRingNegativeProduct
/-!
概要：実乗法の全整数次数成分と標準 tensor の各次数への降下。
方針：元の実写像と係数環同型、次数移送を保持して比較する。
規約：単体環の可換性・対象宇宙の縮小を要求しない。使われ方：β5(g)。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open scoped TensorProduct
open CategoryTheory MonoidalCategory
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.integerCoefficientModuleFunctor
def simplicialRingDGCochainDegreeProduct (A : SimplicialObject RingCat.{u}) (i j : ℤ) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X i ⊗
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X j ⟶
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X (i + j) :=
  if hi : i ≤ 0 then
    if hj : j ≤ 0 then
      ((eqToHom (congrArg (fun k ↦ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X k)
          (show i = -((-i).toNat : ℤ) by omega))) ⊗ₘ
        (eqToHom (congrArg (fun k ↦ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X k)
          (show j = -((-j).toNat : ℤ) by omega)))) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct A (-i).toNat (-j).toNat ≫
      eqToHom (congrArg (fun k ↦ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X k)
        (show -(((-i).toNat + (-j).toNat : ℕ) : ℤ) = i + j by omega))
    else 0
  else 0

lemma simplicialRingDGCochainDegreeProduct_positive_left
    (A : SimplicialObject RingCat.{u}) (i j : ℤ) (hi : 0 < i) :
    simplicialRingDGCochainDegreeProduct A i j = 0 := by
  simp only [simplicialRingDGCochainDegreeProduct, dite_eq_right (by omega : ¬i ≤ 0)]

lemma simplicialRingDGCochainDegreeProduct_positive_right
    (A : SimplicialObject RingCat.{u}) (i j : ℤ) (hj : 0 < j) :
    simplicialRingDGCochainDegreeProduct A i j = 0 := by
  unfold simplicialRingDGCochainDegreeProduct
  split
  · exact dite_eq_right (by omega)
  · rfl


lemma simplicialRingDGCochainDegreeProduct_negative
    (A : SimplicialObject RingCat.{u}) (p q : ℕ) :
    simplicialRingDGCochainDegreeProduct A (-(p : ℤ)) (-(q : ℤ)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct A p q ≫
        eqToHom (congrArg (fun k ↦ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X k)
          (show -((p + q : ℕ) : ℤ) = -(p : ℤ) + -(q : ℤ) by omega)) := by
  have hp : -(p : ℤ) ≤ 0 := by omega
  have hq : -(q : ℤ) ≤ 0 := by omega
  simp only [simplicialRingDGCochainDegreeProduct, dite_eq_left hp, dite_eq_left hq]
  apply eq_of_heq
  simp only [tensorHom_def, eqToHom_whiskerRight, whiskerLeft_eqToHom,
    Category.assoc, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
    heq_comp_eqToHom_iff]
  congr! 1 <;> omega


def simplicialRingDGCochainMultiplicationComponent
    (A : SimplicialObject RingCat.{u}) (n : ℤ) :
    (SerrePositivity.cochainTensor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A)).X n ⟶
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X n :=
  HomologicalComplex.mapBifunctorDesc (fun i j h ↦
    simplicialRingDGCochainDegreeProduct A i j ≫
      eqToHom (congrArg (fun k ↦ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X k) h))

lemma simplicialRingDGCochainMultiplicationComponent_bidegree
    (A : SimplicialObject RingCat.{u}) (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιTensorObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A) i j n h ≫
      simplicialRingDGCochainMultiplicationComponent A n =
        simplicialRingDGCochainDegreeProduct A i j ≫
          eqToHom (congrArg (fun k ↦ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X k) h) :=
  HomologicalComplex.ι_mapBifunctorDesc _ i j h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
