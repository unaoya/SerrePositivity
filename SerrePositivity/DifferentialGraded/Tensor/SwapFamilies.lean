module
public import SerrePositivity.DifferentialGraded.Tensor.BalancedReindex
public import SerrePositivity.DifferentialGraded.Module.LeftActionComparison

/-! # opposite上のbalanced族の符号付き交換 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- opposite側の族をsigned braidingで元のtensor順序へ戻す。 -/
def swapFamilyApp (M : RightModule A D) (N : LeftModule A D) {T : Complex A}
    (b : ∀ x, objectFamily A Dᵒᵖ N.toRightOpposite M.toFunctor x ⟶ T) (x : D) :
    objectFamily A D M N x ⟶ T :=
  (signedSwap (M.obj (op x)) (N.obj x)).hom ≫ b (op x)

lemma swapFamilyApp_element (M : RightModule A D) (N : LeftModule A D) {T : Complex A}
    (b : ∀ x, objectFamily A Dᵒᵖ N.toRightOpposite M.toFunctor x ⟶ T) (x : D)
    {r s n : ℤ} (m : (M.obj (op x)).X r) (t : (N.obj x).X s) (hn : r + s = n) :
    familyElement A D (swapFamilyApp A D M N b) x m t hn =
      (r * s).negOnePow • familyElement A Dᵒᵖ b (op x) t m (by omega) := by
  change (b (op x)).f n ((signedSwap (M.obj (op x)) (N.obj x)).hom.f n
    (ιTensorObj (M.obj (op x)) (N.obj x) r s n hn (m ⊗ₜ[A] t))) = _
  rw [signedSwap_apply]
  simp only [familyElement, Units.smul_def, map_zsmul]
  rfl

/-- 元の族をsigned braidingでopposite上のtensor順序へ移す。 -/
def unswapFamilyApp (M : RightModule A D) (N : LeftModule A D) {T : Complex A}
    (a : ∀ x, objectFamily A D M N x ⟶ T) (x : Dᵒᵖ) :
    objectFamily A Dᵒᵖ N.toRightOpposite M.toFunctor x ⟶ T :=
  (signedSwap (N.obj x.unop) (M.obj x)).hom ≫ a x.unop

lemma unswapFamilyApp_element (M : RightModule A D) (N : LeftModule A D) {T : Complex A}
    (a : ∀ x, objectFamily A D M N x ⟶ T) (x : Dᵒᵖ)
    {s r n : ℤ} (t : (N.obj x.unop).X s) (m : (M.obj x).X r) (hn : s + r = n) :
    familyElement A Dᵒᵖ (unswapFamilyApp A D M N a) x t m hn =
      (s * r).negOnePow • familyElement A D a x.unop m t (by omega) := by
  change (a x.unop).f n ((signedSwap (N.obj x.unop) (M.obj x)).hom.f n
    (ιTensorObj (N.obj x.unop) (M.obj x) s r n hn (t ⊗ₜ[A] m))) = _
  rw [signedSwap_apply]
  simp only [familyElement, Units.smul_def, map_zsmul]

/-- opposite上のbalanced族から元のbalanced族へ。 -/
def swapFamily (M : RightModule A D) (N : LeftModule A D) {T : Complex A}
    (b : BalancedFamily A Dᵒᵖ N.toRightOpposite M.toFunctor T) : BalancedFamily A D M N T := by
  refine balancedFamilyMk A D (swapFamilyApp A D M N b.val) ?_
  intro x y r p s n hn m f t
  rw [swapFamilyApp_element, swapFamilyApp_element]
  have hb := balancedFamily_element_of_sums A Dᵒᵖ b (op y) (op x)
    (i := p + s) (j := r + p) (n := n) (by omega) rfl (by omega) t f m
  rw [leftToRightOpposite_action, rightToLeft_action] at hb
  rw [← hb]
  simp only [smul_smul, ← Int.negOnePow_add]
  have hs : r * p + ((r + p) * s + s * p) = r * (p + s) + 2 * (p * s) := by ring
  rw [hs, Int.negOnePow_add (r * (p + s)) (2 * (p * s)), Int.negOnePow_two_mul, mul_one]

/-- 元のbalanced族からopposite上のbalanced族へ。 -/
def unswapFamily (M : RightModule A D) (N : LeftModule A D) {T : Complex A}
    (a : BalancedFamily A D M N T) : BalancedFamily A Dᵒᵖ N.toRightOpposite M.toFunctor T := by
  refine balancedFamilyMk A Dᵒᵖ (unswapFamilyApp A D M N a.val) ?_
  intro x y s p r n hn t f m
  rw [unswapFamilyApp_element, unswapFamilyApp_element,
    leftToRightOpposite_action, rightToLeft_action]
  have ha := balancedFamily_element_of_sums A D a y.unop x.unop
    (i := p + r) (j := s + p) (n := n) (by omega) rfl (by omega) m f t
  rw [← ha]
  simp only [smul_smul, ← Int.negOnePow_add]
  have hs : s * p + ((s + p) * r + r * p) = s * (p + r) + 2 * (r * p) := by ring
  rw [hs, Int.negOnePow_add (s * (p + r)) (2 * (r * p)), Int.negOnePow_two_mul, mul_one]

/-- 符号付き交換はbalanced族の同値を与える。 -/
def swapFamilyEquiv (M : RightModule A D) (N : LeftModule A D) (T : Complex A) :
    BalancedFamily A D M N T ≃ BalancedFamily A Dᵒᵖ N.toRightOpposite M.toFunctor T where
  toFun := unswapFamily A D M N
  invFun := swapFamily A D M N
  left_inv a := by
    apply Subtype.ext
    funext x
    change (signedSwap (M.obj (op x)) (N.obj x)).hom ≫
      (signedSwap (N.obj x) (M.obj (op x))).hom ≫ a.val x = a.val x
    rw [← Category.assoc, SerrePositivity.cochainTensorSymmetry_hom_comp]
    exact Category.id_comp _
  right_inv b := by
    apply Subtype.ext
    funext x
    change (signedSwap (N.obj x.unop) (M.obj x)).hom ≫
      (signedSwap (M.obj x) (N.obj x.unop)).hom ≫ b.val x = b.val x
    rw [← Category.assoc, SerrePositivity.cochainTensorSymmetry_hom_comp]
    exact Category.id_comp _

end SerrePositivity.DifferentialGraded.BalancedTensor
