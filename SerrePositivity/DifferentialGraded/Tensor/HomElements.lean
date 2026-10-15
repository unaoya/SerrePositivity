module
public import SerrePositivity.DifferentialGraded.Tensor.ParameterRight
public import SerrePositivity.DifferentialGraded.Tensor.ParameterLeft
public import SerrePositivity.DifferentialGraded.Tensor.ElementsExt

/-! # balanced tensorの左右主Hom写像の全次数成分 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma rightHomMap_element {M M' : RightModule A D} (N : LeftModule A D)
    {k r s n : ℤ} (τ : (moduleHom A D M M').X k) (x : D)
    (m : (M.obj (op x)).X r) (v : (N.obj x).X s) (hn : r + s + k = n) :
    (((rightHomMap A D M M' N).f k τ).v (r + s) n hn)
      (element A D M N x m v rfl) =
    element A D M' N x (((moduleHomπ A D M M' x).f k τ).v r (k + r) (by omega) m) v
      (by omega) := by
  change (curryComponent (rightParamMap A D N (fun y => moduleHomπ A D M M' y.unop)
    (moduleHomπ_naturality A D M M')) k τ).v (r + s) n hn _ = _
  rw [curryComponent_apply]
  exact rightParamMap_element A D N (fun y => moduleHomπ A D M M' y.unop)
    (moduleHomπ_naturality A D M M') x τ m v (by omega)

lemma leftHomMap_element (M : RightModule A D) {N N' : LeftModule A D}
    {k r s n : ℤ} (τ : (leftModuleHom A D N N').X k) (x : D)
    (m : (M.obj (op x)).X r) (v : (N.obj x).X s) (hn : r + s + k = n) :
    (((leftHomMap A D M N N').f k τ).v (r + s) n hn)
      (element A D M N x m v rfl) =
    (k * r).negOnePow • element A D M N' x m
      (((leftModuleHomπ A D N N' x).f k τ).v s (k + s) (by omega) v) (by omega) := by
  change (curryComponent (leftParamMap A D M (leftModuleHomπ A D N N')
    (leftModuleHomπ_naturality A D N N')) k τ).v (r + s) n hn _ = _
  rw [curryComponent_apply]
  exact leftParamMap_element A D M (leftModuleHomπ A D N N')
    (leftModuleHomπ_naturality A D N N') x τ m v (by omega)

lemma rightHomMap_element_of_sum {M M' : RightModule A D} (N : LeftModule A D)
    {k r s a l n : ℤ} (τ : (moduleHom A D M M').X k) (x : D)
    (m : (M.obj (op x)).X r) (v : (N.obj x).X s)
    (ha : r + s = a) (hl : k + r = l) (hn : a + k = n) :
    (((rightHomMap A D M M' N).f k τ).v a n hn) (element A D M N x m v ha) =
    element A D M' N x (((moduleHomπ A D M M' x).f k τ).v r l (by omega) m) v
      (by omega) := by
  subst a l
  exact rightHomMap_element A D N τ x m v hn

lemma leftHomMap_element_of_sum (M : RightModule A D) {N N' : LeftModule A D}
    {k r s a l n : ℤ} (τ : (leftModuleHom A D N N').X k) (x : D)
    (m : (M.obj (op x)).X r) (v : (N.obj x).X s)
    (ha : r + s = a) (hl : k + s = l) (hn : a + k = n) :
    (((leftHomMap A D M N N').f k τ).v a n hn) (element A D M N x m v ha) =
    (k * r).negOnePow • element A D M N' x m
      (((leftModuleHomπ A D N N' x).f k τ).v s l (by omega) v) (by omega) := by
  subst a l
  exact leftHomMap_element A D M τ x m v hn

lemma element_units_smul_right (M : RightModule A D) (N : LeftModule A D) (x : D)
    {r s n : ℤ} (u : ℤˣ) (m : (M.obj (op x)).X r) (v : (N.obj x).X s) (hn : r + s = n) :
    element A D M N x m (u • v) hn = u • element A D M N x m v hn := by
  have ht : m ⊗ₜ[A] (u • v) = u • (m ⊗ₜ[A] v) :=
    map_zsmul (TensorProduct.mk A _ _ m) (u : ℤ) v
  unfold element
  rw [ht]
  simp only [Units.smul_def, map_zsmul]

end SerrePositivity.DifferentialGraded.BalancedTensor
