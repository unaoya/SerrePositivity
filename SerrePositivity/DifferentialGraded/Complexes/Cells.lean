module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.Algebra.Homology.Double

/-! # コチェインの sphere/disk と生成元の指定

sphere n は次数nのA、disk n は次数n→n+1の恒等微分。
セルの境界包含は sphere (n+1)→disk n。この規約をホモロジー次数と混同しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A]

/-- Aからの線形射は1の像で指定できる。 -/
def moduleElementMap (V : ModuleCat.{u} A) (z : V) : (𝟙_ (ModuleCat A)) ⟶ V :=
  ModuleCat.ofHom
    { toFun := fun a => a • z
      map_add' a b := add_smul a b z
      map_smul' a b := mul_smul a b z }

def moduleElementEquiv (V : ModuleCat.{u} A) : ((𝟙_ (ModuleCat A)) ⟶ V) ≃ V where
  toFun f := f (1 : A)
  invFun := moduleElementMap A V
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change a • f (1 : A) = f a
    rw [← map_smul]
    congr 1
    simp
  right_inv z := by change (1 : A) • z = z; exact one_smul A z

/-- 一つの次数nに集中したA複体。 -/
abbrev complexSphere (n : ℤ) : Complex A :=
  (single (ModuleCat A) (.up ℤ) n).obj (𝟙_ (ModuleCat A))

/-- 次数n→n+1の恒等微分からなるdisk。 -/
abbrev complexDisk (n : ℤ) : Complex A :=
  double (𝟙 (𝟙_ (ModuleCat A))) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)

/-- 次数nのcycleを要素として扱う。 -/
abbrev complexCycles (K : Complex A) (n : ℤ) := LinearMap.ker (K.d n (n + 1)).hom

abbrev complexDiskX₀ (n : ℤ) : (complexDisk A n).X n ≅ (𝟙_ (ModuleCat A)) :=
  doubleXIso₀ _ _

abbrev complexDiskX₁ (n : ℤ) : (complexDisk A n).X (n + 1) ≅ (𝟙_ (ModuleCat A)) :=
  doubleXIso₁ _ _ (by omega)

/-- diskからのchain mapは次数nの任意の生成元の像で指定できる。 -/
def complexDiskHomEquiv (K : Complex A) (n : ℤ) : (complexDisk A n ⟶ K) ≃ K.X n :=
  (evalCompCoyonedaCorepresentableByDoubleId
    (show (ComplexShape.up ℤ).Rel n (n + 1) by simp) (by omega) (𝟙_ (ModuleCat A))).homEquiv.trans
      (moduleElementEquiv A (K.X n))

/-- sphereからの射の生成元の像はcycle。 -/
def complexSphereCycle {K : Complex A} (n : ℤ) (f : complexSphere A n ⟶ K) :
    complexCycles A K n where
  val := ((singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv ≫ f.f n) (1 : A)
  property := by
    have hc := f.comm n (n + 1)
    change f.f n ≫ K.d n (n + 1) =
      ((single (ModuleCat A) (.up ℤ) n).obj (𝟙_ (ModuleCat A))).d n (n + 1) ≫ f.f (n + 1) at hc
    rw [single_obj_d, zero_comp] at hc
    have h := congrArg (fun φ =>
      ((singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv ≫ φ) (1 : A)) hc
    change K.d n (n + 1)
      (((singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv ≫ f.f n) (1 : A)) = 0 at h
    exact h

/-- cycleを指定したsphereからの射。 -/
def complexSphereMap {K : Complex A} (n : ℤ) (z : complexCycles A K n) : complexSphere A n ⟶ K :=
  mkHomFromSingle (moduleElementMap A (K.X n) z.val) (by
    intro k hk
    obtain rfl : k = n + 1 := hk.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change K.d n (n + 1) (a • z.val) = 0
    rw [map_smul, z.property, smul_zero])

/-- sphereからのchain mapは次数nのcycleの像で指定できる。 -/
def complexSphereHomEquiv (K : Complex A) (n : ℤ) :
    (complexSphere A n ⟶ K) ≃ complexCycles A K n where
  toFun := complexSphereCycle A n
  invFun := complexSphereMap A n
  left_inv f := by
    apply from_single_hom_ext
    apply (cancel_epi (singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv).1
    rw [complexSphereMap, mkHomFromSingle_f, Iso.inv_hom_id_assoc]
    exact (moduleElementEquiv A (K.X n)).left_inv
      ((singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv ≫ f.f n)
  right_inv z := by
    apply Subtype.ext
    change ((singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv ≫
      (complexSphereMap A n z).f n) (1 : A) = z.val
    rw [complexSphereMap, mkHomFromSingle_f, Iso.inv_hom_id_assoc]
    exact one_smul A z.val

/-- cochain diskの境界は上の次数n+1のsphere。 -/
def complexSphereToDisk (n : ℤ) : complexSphere A (n + 1) ⟶ complexDisk A n :=
  mkHomFromSingle (complexDiskX₁ A n).inv (by
    intro k _
    rw [double_d_eq_zero₀ _ _ (n + 1) k (by omega), comp_zero])

lemma complexDiskHomEquiv_apply {K : Complex A} (n : ℤ) (f : complexDisk A n ⟶ K) :
    complexDiskHomEquiv A K n f = ((complexDiskX₀ A n).inv ≫ f.f n) (1 : A) := rfl

lemma complexDiskHomEquiv_naturality {K L : Complex A} (n : ℤ)
    (f : complexDisk A n ⟶ K) (g : K ⟶ L) :
    complexDiskHomEquiv A L n (f ≫ g) = g.f n (complexDiskHomEquiv A K n f) := by
  rw [complexDiskHomEquiv_apply, HomologicalComplex.comp_f, complexDiskHomEquiv_apply]
  rfl

/-- diskの上の生成元の像は、下の生成元の像の微分。 -/
lemma complexDisk_upper_apply {K : Complex A} (n : ℤ) (f : complexDisk A n ⟶ K) :
    ((complexDiskX₁ A n).inv ≫ f.f (n + 1)) (1 : A) =
      K.d n (n + 1) (complexDiskHomEquiv A K n f) := by
  have hc := f.comm n (n + 1)
  change f.f n ≫ K.d n (n + 1) =
    (double _ (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)).d n (n + 1) ≫ f.f (n + 1) at hc
  rw [double_d _ _ (by omega)] at hc
  have hh := congrArg (fun φ => (complexDiskX₀ A n).inv ≫ φ) hc
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Category.id_comp] at hh
  have hv := congrArg (fun φ => φ (1 : A)) hh
  change K.d n (n + 1) (((complexDiskX₀ A n).inv ≫ f.f n) (1 : A)) =
    ((complexDiskX₁ A n).inv ≫ f.f (n + 1)) (1 : A) at hv
  exact hv.symm

/-- セル境界包含による前合成は生成元の微分を取る操作。 -/
lemma complexSphereToDisk_comp {K : Complex A} (n : ℤ) (f : complexDisk A n ⟶ K) :
    (complexSphereHomEquiv A K (n + 1) (complexSphereToDisk A n ≫ f)).val =
      K.d n (n + 1) (complexDiskHomEquiv A K n f) := by
  change (((singleObjXSelf (.up ℤ) (n + 1) (𝟙_ (ModuleCat A))).inv) ≫
    (complexSphereToDisk A n ≫ f).f (n + 1)) (1 : A) = _
  rw [HomologicalComplex.comp_f, complexSphereToDisk, mkHomFromSingle_f,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact complexDisk_upper_apply A n f

end SerrePositivity.DifferentialGraded
