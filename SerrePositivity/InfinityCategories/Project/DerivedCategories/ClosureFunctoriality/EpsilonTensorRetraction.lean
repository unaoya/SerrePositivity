module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.EpsilonTensorSeparation

/-!
概要：ε を前置した tensor 成分を、先頭単位の係数で明示的に取り出す。
方針：二次数射影で 0／−1／q を選び、二つの単位係数を縮約する。
規約：次数ごとの加群射であり、商の微分との可換性は要求しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R]

/-- tensor の第一因子の係数を取る加群射。 -/
def tensorLeftCoefficient (M N : ModuleCat R) (l : M →ₗ[R] R) : M ⊗ N ⟶ N :=
  ModuleCat.ofHom ((TensorProduct.lid R N).toLinearMap.comp
    (TensorProduct.map l (LinearMap.id : N →ₗ[R] N)))

lemma tensorLeftCoefficient_tmul (M N : ModuleCat R) (l : M →ₗ[R] R) (a : M) (b : N) :
    tensorLeftCoefficient R M N l (a ⊗ₜ[R] b) = l a • b := by
  change (TensorProduct.lid R N) (TensorProduct.map l LinearMap.id (a ⊗ₜ[R] b)) = _
  rw [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul]

variable (K L : Complex R)

/-- 単位・ε・末尾の次数 q を順に読む次数別射影。 -/
def epsilonTensorLeftRetraction (q : ℤ) (l : K.X 0 →ₗ[R] R) :
    (K ⊗ (complexSphere R (-1) ⊗ L)).X ((-1) + q) ⟶ L.X q :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.tensorDegreeProjection R K (complexSphere R (-1) ⊗ L) 0 ((-1) + q) ((-1) + q) ≫
    tensorLeftCoefficient R (K.X 0) ((complexSphere R (-1) ⊗ L).X ((-1) + q)) l ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.tensorDegreeProjection R (complexSphere R (-1)) L (-1) q ((-1) + q) ≫
    tensorLeftCoefficient R ((complexSphere R (-1)).X (-1)) (L.X q)
      (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat R))).hom.hom

/-- ε 前置項に対する係数射影は、元の末尾を厳密に回収する。 -/
lemma epsilonTensorLeftRetraction_apply (q : ℤ) (l : K.X 0 →ₗ[R] R)
    (a : K.X 0) (ha : l a = 1) (z : L.X q) :
    epsilonTensorLeftRetraction R K L q l (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilonTensorLeft R K L q a z) = z := by
  have ho := ConcreteCategory.congr_hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.tensorDegreeProjection_split R K (complexSphere R (-1) ⊗ L)
      0 ((-1) + q) ((-1) + q) (zero_add _))
    (a ⊗ₜ[R] ιTensorObj (complexSphere R (-1)) L (-1) q ((-1) + q) rfl
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat R))).inv (1 : R) ⊗ₜ[R] z))
  have hi := ConcreteCategory.congr_hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.tensorDegreeProjection_split R (complexSphere R (-1)) L (-1) q ((-1) + q) rfl)
    ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat R))).inv (1 : R) ⊗ₜ[R] z)
  have hu := ConcreteCategory.congr_hom
    (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat R))).inv_hom_id (1 : R)
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at ho hi hu
  simp only [epsilonTensorLeftRetraction, ModuleCat.comp_apply]
  rw [show _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.tensorDegreeProjection R K (complexSphere R (-1) ⊗ L)
      0 ((-1) + q) ((-1) + q) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilonTensorLeft R K L q a z) = _ from ho]
  rw [tensorLeftCoefficient_tmul, ha, one_smul]
  rw [show _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.tensorDegreeProjection R (complexSphere R (-1)) L (-1) q ((-1) + q)
    (ιTensorObj (complexSphere R (-1)) L (-1) q ((-1) + q) rfl
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat R))).inv (1 : R) ⊗ₜ[R] z)) = _ from hi]
  rw [tensorLeftCoefficient_tmul]
  change ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat R))).hom
    ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat R))).inv (1 : R))) • z = z
  rw [hu, one_smul]

/-- 先頭次数が零でない項は、この射影では零になる。 -/
lemma epsilonTensorLeftRetraction_other_degree (q p j : ℤ) (h : p + j = (-1) + q)
    (hp : p ≠ 0) (l : K.X 0 →ₗ[R] R)
    (t : (K.X p ⊗ (complexSphere R (-1) ⊗ L).X j : ModuleCat R)) :
    epsilonTensorLeftRetraction R K L q l
      (ιTensorObj K (complexSphere R (-1) ⊗ L) p j ((-1) + q) h t) = 0 := by
  have ht := ConcreteCategory.congr_hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.tensorDegreeProjection_other R K (complexSphere R (-1) ⊗ L)
      0 ((-1) + q) p j ((-1) + q) h hp) t
  simp only [epsilonTensorLeftRetraction, ModuleCat.comp_apply]
  rw [show _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.tensorDegreeProjection R K (complexSphere R (-1) ⊗ L)
    0 ((-1) + q) ((-1) + q)
    (ιTensorObj K (complexSphere R (-1) ⊗ L) p j ((-1) + q) h t) = 0 from ht]
  simp

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
