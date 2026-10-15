module
public import SerrePositivity.DifferentialGraded.Tensor.FubiniData
public import SerrePositivity.DifferentialGraded.Tensor.BalancedFamilyElements

/-! # 二つの作用についてbalancedな三重tensor族の左反復coendへの降下 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

abbrev TripleFamily (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C)
    (T : Complex A) := ∀ (c : C) (e : E), R.obj (op e) ⊗ (Q.value c e ⊗ N.obj c) ⟶ T

def tripleElement {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : TripleFamily A C E Q R N T) (c : C) (e : E)
    {k r s i n : ℤ} (t : (R.obj (op e)).X k) (q : (Q.value c e).X r) (v : (N.obj c).X s)
    (hi : r + s = i) (hn : k + i = n) : T.X n :=
  (a c e).f n (ιTensorObj (R.obj (op e)) (Q.value c e ⊗ N.obj c) k i n hn
    (t ⊗ₜ[A] ιTensorObj (Q.value c e) (N.obj c) r s i hi (q ⊗ₜ[A] v)))

/-- 内側Cのbalanced条件と、外側Eの全次数balanced関係を保持する族。 -/
@[ext] structure DoubleFamily (Q : Bimodule A C E) (R : RightModule A E)
    (N : LeftModule A C) (T : Complex A) where
  row : ∀ e : E, ParamFamily A C (Q.rightAt e) N (R.obj (op e)) T
  balanceE : ∀ (c : C) (e e' : E) (k p r s n : ℤ) (hn : k + p + (r + s) = n)
    (t : (R.obj (op e')).X k) (f : GradedHom A e e' p)
    (q : (Q.value c e).X r) (v : (N.obj c).X s),
    (k * p).negOnePow • tripleElement A C E (n := n) (fun c e => (row e).val c) c e
      (moduleAction A R f t rfl) q v rfl (by omega) =
    tripleElement A C E (n := n) (fun c e => (row e).val c) c e' t
      (SerrePositivity.DifferentialGraded.leftAction A (Q.leftAt c) f q rfl) v rfl (by omega)

omit [Small.{u} E] in
/-- 内側の降下後も、Eのbalanced関係は全cochainの等式として残る。 -/
lemma rowCurry_balanceE {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) (e e' : E) (k p : ℤ)
    (t : (R.obj (op e')).X k) (f : GradedHom A e e' p) :
    (k * p).negOnePow • (curryRight (paramDesc A C (Q.rightAt e) N (a.row e))).f (k + p)
      (moduleAction A R f t rfl) =
    (((leftModule A C E Q N).map e e').f p f).comp
      ((curryRight (paramDesc A C (Q.rightAt e') N (a.row e'))).f k t) (by omega) := by
  apply cochain_element_ext A C (Q.rightAt e) N
  intro c r s i n hi hn q v
  subst i
  rw [Cochain.units_smul_v, Cochain.comp_v _ _ (by omega : p + k = k + p)
    (r + s) (r + p + s) n (by omega) (by omega)]
  change (k * p).negOnePow •
      (((curryRight (paramDesc A C (Q.rightAt e) N (a.row e))).f (k + p)
        (moduleAction A R f t rfl)).v (r + s) n hn (element A C (Q.rightAt e) N c q v rfl)) =
    ((curryRight (paramDesc A C (Q.rightAt e') N (a.row e'))).f k t).v (r + p + s) n (by omega)
      (SerrePositivity.DifferentialGraded.leftAction A (leftModule A C E Q N) f
        (element A C (Q.rightAt e) N c q v rfl) (by omega))
  rw [leftModule_action_element A C E Q N e e' c (j := r + p) rfl rfl (by omega) f q v,
    paramDesc_curry_element, paramDesc_curry_element]
  exact a.balanceE c e e' k p r s n (by omega) t f q v

/-- 二重balanced族を外側Eのbalanced族へ降ろす。 -/
def leftFamily {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) :
    BalancedFamily A E R (leftModule A C E Q N) T := by
  refine balancedFamilyMk A E (fun e => paramDesc A C (Q.rightAt e) N (a.row e)) ?_
  intro e e' k p i n hn t f z
  have h := congrArg (fun c => c.v i n (by omega) z) (rowCurry_balanceE A C E a e e' k p t f)
  rw [Cochain.units_smul_v, Cochain.comp_v _ _ (by omega : p + k = k + p)
    i (p + i) n (by omega) (by omega)] at h
  exact h

/-- 二重balanced族からR⊗_E(Q⊗_C N)への実際の降下。 -/
def leftDesc {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) : leftObj A C E Q R N ⟶ T :=
  desc A E R (leftModule A C E Q N) (leftFamily A C E a)

@[reassoc (attr := simp)]
lemma leftι_leftDesc {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) (c : C) (e : E) :
    leftι A C E Q R N c e ≫ leftDesc A C E a = (a.row e).val c := by
  change (R.obj (op e) ◁ ι A C (Q.rightAt e) N c) ≫
    ι A E R (leftModule A C E Q N) e ≫
      desc A E R (leftModule A C E Q N) (leftFamily A C E a) = _
  rw [ι_desc]
  exact ι_paramDesc A C (Q.rightAt e) N (a.row e) c

/-- 左反復coendの生成元の評価。内側の次数を明示して保持する。 -/
lemma tripleElement_leftι {Q : Bimodule A C E} {R : RightModule A E}
    {N : LeftModule A C} {T : Complex A} (f : leftObj A C E Q R N ⟶ T)
    (c : C) (e : E) {k r s i n : ℤ}
    (t : (R.obj (op e)).X k) (q : (Q.value c e).X r) (v : (N.obj c).X s)
    (hi : r + s = i) (hn : k + i = n) :
    tripleElement A C E (fun c e => leftι A C E Q R N c e ≫ f) c e t q v hi hn =
      familyElement A E (fun e => ι A E R (leftModule A C E Q N) e ≫ f) e t
        (element A C (Q.rightAt e) N c q v hi) hn := by
  change (ι A E R (leftModule A C E Q N) e ≫ f).f n
    ((R.obj (op e) ◁ ι A C (Q.rightAt e) N c).f n _) = _
  rw [whiskerLeft_apply]
  rfl

omit [Small.{u} E] in
/-- 内側coendの総次数の等しい二つの表示は同じ外側の評価を与える。 -/
lemma familyElement_inner_reindex {Q : Bimodule A C E} {R : RightModule A E}
    {N : LeftModule A C} {T : Complex A}
    (a : ∀ e, R.obj (op e) ⊗ (leftModule A C E Q N).obj e ⟶ T) (c : C) (e : E)
    {k r s i j n : ℤ} (t : (R.obj (op e)).X k) (q : (Q.value c e).X r)
    (v : (N.obj c).X s) (hi : r + s = i) (hj : r + s = j)
    (hni : k + i = n) (hnj : k + j = n) :
    familyElement A E a e t (element A C (Q.rightAt e) N c q v hi) hni =
      familyElement A E a e t (element A C (Q.rightAt e) N c q v hj) hnj := by
  subst i j
  rfl

/-- 左反復coendからの射を二重balanced族へ制限する。 -/
def leftRestrict {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (f : leftObj A C E Q R N ⟶ T) : DoubleFamily A C E Q R N T := by
  change obj A E R (leftModule A C E Q N) ⟶ T at f
  refine ⟨fun e => paramRestrict A C (Q.rightAt e) N
    (ι A E R (leftModule A C E Q N) e ≫ f), ?_⟩
  intro c e e' k p r s n hn t g q v
  change (k * p).negOnePow • tripleElement A C E (n := n)
    (fun c e => leftι A C E Q R N c e ≫ f) c e
      (moduleAction A R g t rfl) q v rfl (by omega) =
    tripleElement A C E (n := n) (fun c e => leftι A C E Q R N c e ≫ f) c e' t
      (SerrePositivity.DifferentialGraded.leftAction A (Q.leftAt c) g q rfl) v rfl (by omega)
  rw [tripleElement_leftι, tripleElement_leftι]
  have h := balancedFamily_element A E (homEquiv A E R (leftModule A C E Q N) T f)
    e e' t g (element A C (Q.rightAt e) N c q v rfl) hn
  rw [leftModule_action_element A C E Q N e e' c (j := r + p)
    rfl rfl (by omega) g q v] at h
  exact h.trans (familyElement_inner_reindex A C E
    (fun e => ι A E R (leftModule A C E Q N) e ≫ f) c e'
    (i := p + (r + s)) (j := r + p + s) t
    (SerrePositivity.DifferentialGraded.leftAction A (Q.leftAt c) g q rfl) v
    (by omega) rfl (by omega) (by omega))

/-- 二重balanced族と左反復coendからの射の普遍的同値。 -/
def leftHomEquiv (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C)
    (T : Complex A) : (leftObj A C E Q R N ⟶ T) ≃ DoubleFamily A C E Q R N T where
  toFun := leftRestrict A C E
  invFun := leftDesc A C E
  left_inv f := by
    apply left_hom_ext A C E Q R N
    intro c e
    exact leftι_leftDesc A C E (leftRestrict A C E f) c e
  right_inv a := by
    apply DoubleFamily.ext
    funext e
    apply Subtype.ext
    funext c
    exact leftι_leftDesc A C E a c e

end SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
