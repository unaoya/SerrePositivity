module
public import SerrePositivity.DifferentialGraded.Tensor.FubiniRightFamilies
public import SerrePositivity.DifferentialGraded.Tensor.ParameterBalancedConstructor

/-! # 右反復coendから二重balanced族への制限 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

/-- 右反復coendへの三重包含の斉次評価。 -/
lemma tripleElement_rightι {Q : Bimodule A C E} {R : RightModule A E}
    {N : LeftModule A C} {T : Complex A} (f : rightObj A C E Q R N ⟶ T)
    (c : C) (e : E) {k r s i l n : ℤ}
    (t : (R.obj (op e)).X k) (q : (Q.value c e).X r) (v : (N.obj c).X s)
    (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    tripleElement A C E (fun c e => rightι A C E Q R N c e ≫ f) c e t q v hi hn =
    familyElement A C (fun c => ι A C (rightModule A C E Q R) N c ≫ f) c
      (element A E R (Q.leftAt c) e t q hl) v (by omega) := by
  subst l
  change (ι A C (rightModule A C E Q R) N c ≫ f).f n
    ((ι A E R (Q.leftAt c) e ▷ N.obj c).f n
      ((α_ (R.obj (op e)) (Q.value c e) (N.obj c)).inv.f n
        (ιTensorObj (R.obj (op e)) (Q.value c e ⊗ N.obj c) k i n hn
          (t ⊗ₜ[A] ιTensorObj (Q.value c e) (N.obj c) r s i hi (q ⊗ₜ[A] v))))) = _
  rw [associator_inv_apply]
  have h := whiskerRight_apply (ι A E R (Q.leftAt c) e) (N.obj c) (k + r) s n
    (by omega) (ιTensorObj (R.obj (op e)) ((Q.leftAt c).obj e) k r (k + r) rfl
      (t ⊗ₜ[A] q)) v
  exact congrArg (fun z => (ι A C (rightModule A C E Q R) N c ≫ f).f n z) h

/-- balanced族の評価は第一因子の整数単位スカラーを保存する。 -/
lemma familyElement_units_smul_left {D : Type v} [DGCategory A D]
    {M : RightModule A D} {N : LeftModule A D} {T : Complex A}
    (a : ∀ x, objectFamily A D M N x ⟶ T) (x : D) {r s n : ℤ}
    (u : ℤˣ) (m : (M.obj (op x)).X r) (v : (N.obj x).X s) (hn : r + s = n) :
    familyElement A D a x (u • m) v hn = u • familyElement A D a x m v hn := by
  simp only [familyElement, Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul]

/-- 三重包含から得る族はCについてbalancedである。 -/
lemma rightι_balanceC {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (f : rightObj A C E Q R N ⟶ T) (c c' : C) (e : E)
    (k r p s n : ℤ) (hn : k + (r + p + s) = n)
    (t : (R.obj (op e)).X k) (q : (Q.value c' e).X r)
    (g : GradedHom A c c' p) (v : (N.obj c).X s) :
    (r * p).negOnePow • tripleElement A C E (n := n)
      (fun c e => rightι A C E Q R N c e ≫ f) c e t
      (moduleAction A (Q.rightAt e) g q rfl) v rfl hn =
    tripleElement A C E (i := r + p + s) (n := n)
      (fun c e => rightι A C E Q R N c e ≫ f) c' e t q
      (SerrePositivity.DifferentialGraded.leftAction A N (n := p + s) g v (by omega))
      (by omega) hn := by
  rw [tripleElement_rightι A C E f c e (l := k + r + p),
    tripleElement_rightι A C E f c' e (l := k + r)]
  all_goals try omega
  have h := balancedFamily_element A C (homEquiv A C (rightModule A C E Q R) N T f)
    c c' (element A E R (Q.leftAt c') e t q rfl) g v (by omega : k + r + p + s = n)
  have hact := rightModule_action_element A C E Q R (op c') (op c) e
    (j := r + p) rfl rfl (show k + r + p = k + r + p from rfl) g t q
  rw [hact, familyElement_units_smul_left, smul_smul, ← Int.negOnePow_add] at h
  have hs : (k + r) * p + p * k = r * p + (k * p + k * p) := by ring
  rw [hs, Int.negOnePow_add, Int.negOnePow_add, Int.units_mul_self, mul_one] at h
  exact h

/-- inner E-coendのbalanced関係は作用後の次数を別名で指定できる。 -/
lemma inner_element_balanced_of_sum {Q : Bimodule A C E} {R : RightModule A E}
    (c : C) (e e' : E) {k p r j l : ℤ} (hj : p + r = j) (hl : k + p + r = l)
    (t : (R.obj (op e')).X k) (g : GradedHom A e e' p) (q : (Q.value c e).X r) :
    (k * p).negOnePow • element A E R (Q.leftAt c) e (moduleAction A R g t rfl) q hl =
    element A E R (Q.leftAt c) e' t
      (SerrePositivity.DifferentialGraded.leftAction A (Q.leftAt c) g q (by omega : r + p = j))
      (by omega) := by
  subst j
  exact element_balanced A E R (Q.leftAt c) e e' t g q hl

/-- 三重包含から得る族はEについてもbalancedである。 -/
lemma rightι_balanceE {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (f : rightObj A C E Q R N ⟶ T) (c : C) (e e' : E)
    (k p r s n : ℤ) (hn : k + p + (r + s) = n)
    (t : (R.obj (op e')).X k) (g : GradedHom A e e' p)
    (q : (Q.value c e).X r) (v : (N.obj c).X s) :
    (k * p).negOnePow • tripleElement A C E (n := n)
      (fun c e => rightι A C E Q R N c e ≫ f) c e (moduleAction A R g t rfl) q v rfl (by omega) =
    tripleElement A C E (n := n) (fun c e => rightι A C E Q R N c e ≫ f) c e' t
      (SerrePositivity.DifferentialGraded.leftAction A (Q.leftAt c) (n := r + p) g q rfl)
      v rfl (by omega) := by
  rw [tripleElement_rightι A C E f c e (l := k + p + r),
    tripleElement_rightι A C E f c e' (l := k + p + r)]
  all_goals try omega
  have h := inner_element_balanced_of_sum A C E (Q := Q) (R := R) c e e'
    (j := r + p) (l := k + p + r) (by omega) rfl t g q
  have he := congrArg (fun z => familyElement A C (n := n)
    (fun c => ι A C (rightModule A C E Q R) N c ≫ f) c z v (by omega)) h
  rw [familyElement_units_smul_left] at he
  exact he

/-- 右反復tensorからの射を共通の二重balanced族へ戻す。 -/
def rightRestrict {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (f : rightObj A C E Q R N ⟶ T) : DoubleFamily A C E Q R N T := by
  refine ⟨fun e => paramFamilyMk A C (fun c => rightι A C E Q R N c e ≫ f) ?_, ?_⟩
  · intro c c' k r p s n hn t q g v
    exact rightι_balanceC A C E f c c' e k r p s n hn t q g v
  · intro c e e' k p r s n hn t g q v
    exact rightι_balanceE A C E f c e e' k p r s n hn t g q v

/-- 右反復coendからの射も同じ二重balanced族で表される。 -/
def rightHomEquiv (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C)
    (T : Complex A) : (rightObj A C E Q R N ⟶ T) ≃ DoubleFamily A C E Q R N T where
  toFun := rightRestrict A C E
  invFun := rightDesc A C E
  left_inv f := by
    apply right_hom_ext A C E Q R N
    intro c e
    exact rightι_rightDesc A C E (rightRestrict A C E f) c e
  right_inv a := by
    apply DoubleFamily.ext
    funext e
    apply Subtype.ext
    funext c
    exact rightι_rightDesc A C E a c e

end SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
