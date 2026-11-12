module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.TensorDegreeSeparation
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
概要：単一収縮記号を持つ tensor 項で、先頭単位の次数を用いて成分を分離する。
方針：二次数射影と、単位係数を読む線形汎関数による tensor 消去を使う。
規約：全次数の斉次元に関する計算。微分との可換性は使わない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R] (K L : Complex R)

/-- 先頭の次数零元、指定 ε、末尾元を、同じ全次数の tensor 項へ入れる。 -/
def epsilonTensorLeft (q : ℤ) (a : K.X 0) (z : L.X q) :
    (K ⊗ (complexSphere R (-1) ⊗ L)).X ((-1) + q) :=
  ιTensorObj K (complexSphere R (-1) ⊗ L) 0 ((-1) + q) ((-1) + q) (zero_add _)
    (a ⊗ₜ[R] ιTensorObj (complexSphere R (-1)) L (-1) q ((-1) + q) rfl
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat R))).inv (1 : R) ⊗ₜ[R] z))

/-- 末尾の次数零元の直前へ ε を置く、同じ全次数の項。 -/
def epsilonTensorRight (q : ℤ) (z : K.X q) (a : L.X 0) :
    (K ⊗ (complexSphere R (-1) ⊗ L)).X ((-1) + q) :=
  ιTensorObj K (complexSphere R (-1) ⊗ L) q (-1) ((-1) + q) (by omega)
    (z ⊗ₜ[R] ιTensorObj (complexSphere R (-1)) L (-1) 0 (-1) (by omega)
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat R))).inv (1 : R) ⊗ₜ[R] a))

/-- 先頭元の係数が 1 なら、ε 左項の消滅から末尾元の消滅を回収できる。 -/
lemma epsilonTensorLeft_eq_zero
    (q : ℤ) (l : K.X 0 →ₗ[R] R) (a : K.X 0) (ha : l a = 1) (z : L.X q)
    (h : epsilonTensorLeft R K L q a z = 0) : z = 0 := by
  have hout : a ⊗ₜ[R]
      ιTensorObj (complexSphere R (-1)) L (-1) q ((-1) + q) rfl
        ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat R))).inv (1 : R) ⊗ₜ[R] z) = 0 := by
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.tensorDegreeInclusion_injective R K (complexSphere R (-1) ⊗ L)
      0 ((-1) + q) ((-1) + q) (zero_add _)
    simpa only [epsilonTensorLeft, map_zero] using h
  have hin := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.tensor_left_cancel_of_coefficient R l a ha _ hout
  have ht : (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat R))).inv (1 : R) ⊗ₜ[R] z = 0 := by
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.tensorDegreeInclusion_injective R (complexSphere R (-1)) L (-1) q ((-1) + q) rfl
    simpa only [map_zero] using hin
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.tensor_left_cancel_of_coefficient R
    (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat R))).hom.hom _
    (ConcreteCategory.congr_hom (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat R))).inv_hom_id
      (1 : R)) z ht

/-- ε 左項が先頭次数 q ≠ 0 の項に等しければ、その候補成分は零。 -/
lemma epsilonTensorLeft_eq_other_degree
    (q : ℤ) (hq : q ≠ 0) (l : K.X 0 →ₗ[R] R) (a : K.X 0) (ha : l a = 1)
    (z : L.X q)
    (b : (K.X q ⊗ (complexSphere R (-1) ⊗ L).X (-1) : ModuleCat R))
    (h : epsilonTensorLeft R K L q a z =
      ιTensorObj K (complexSphere R (-1) ⊗ L) q (-1) ((-1) + q) (by omega) b) : z = 0 := by
  apply epsilonTensorLeft_eq_zero R K L q l a ha z
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.tensorDegree_separation R K (complexSphere R (-1) ⊗ L)
    0 ((-1) + q) q (-1) ((-1) + q) (zero_add _) (by omega) hq _ b h
  unfold epsilonTensorLeft
  rw [ht, map_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
