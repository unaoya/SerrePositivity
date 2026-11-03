module

public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import SerrePositivity.DifferentialGraded.Bimodule.Basic
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import SerrePositivity.DifferentialGraded.Tensor.Parameter

/-!
# Tensor.Fubini

## 概要
8 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## RightUnit（旧 SerrePositivity/DifferentialGraded/Tensor/RightUnit.lean） -/

/-! # 対角bimoduleとの右単位比較 -/

@[expose] public section RightUnit
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- 各B対象での右単位はrepresentable tensorのYoneda同型。 -/
def rightUnitValueIso (P : Bimodule A B C) (b : B) (c : C) :
    (compose A B C C P (Bimodule.diagonal A C)).value b c ≅ P.value b c :=
  BalancedTensor.yonedaIso A C c (P.leftAt b)

/-- 右単位の比較は右Bの全Homに関して自然。 -/
lemma rightUnitValue_naturality (P : Bimodule A B C) (b b' : Bᵒᵖ) (c : C) :
    ((compose A B C C P (Bimodule.diagonal A C)).rightAt c).map b b' ≫
      homPostcompose ((compose A B C C P (Bimodule.diagonal A C)).value b.unop c)
        (rightUnitValueIso A B C P b'.unop c).hom =
    (P.rightAt c).map b b' ≫
      homPrecompose (rightUnitValueIso A B C P b.unop c).hom (P.value b'.unop c) := by
  change (P.transposeHom b b' ≫
      BalancedTensor.leftHomMap A C (representable A c) (P.leftAt b.unop) (P.leftAt b'.unop)) ≫
        homPostcompose (BalancedTensor.obj A C (representable A c) (P.leftAt b.unop))
          (BalancedTensor.yonedaEvaluation A C c (P.leftAt b'.unop)) =
    (P.rightAt c).map b b' ≫
      homPrecompose (BalancedTensor.yonedaEvaluation A C c (P.leftAt b.unop)) (P.value b'.unop c)
  rw [Category.assoc, BalancedTensor.yonedaEvaluation_enriched_naturality, ← Category.assoc]
  change (P.transposeHom b b' ≫ moduleHomπ A Cᵒᵖ
      (P.leftAt b.unop).toRightOpposite (P.leftAt b'.unop).toRightOpposite (op c)) ≫ _ = _
  rw [Bimodule.transposeHom_π]
  rfl

/-- 全次数自然な成分同型を実際の右B加群同型へ束ねる。 -/
def rightUnitIso (P : Bimodule A B C) (c : C) :
    ForgetEnrichment.of (Complex A) ((compose A B C C P (Bimodule.diagonal A C)).rightAt c) ≅
      ForgetEnrichment.of (Complex A) (P.rightAt c) :=
  moduleIsoMk A B (fun b => rightUnitValueIso A B C P b.unop c)
    (fun b b' => rightUnitValue_naturality A B C P b b' c)

@[simp]
lemma rightUnitIso_hom_eval (P : Bimodule A B C) (b : B) (c : C) :
    (moduleEvaluation A B b).map
      (X := ForgetEnrichment.of (Complex A)
        ((compose A B C C P (Bimodule.diagonal A C)).rightAt c))
      (Y := ForgetEnrichment.of (Complex A) (P.rightAt c)) (rightUnitIso A B C P c).hom =
      (rightUnitValueIso A B C P b c).hom :=
  moduleIsoMk_hom_eval A B _ _ b

@[simp]
lemma rightUnitIso_inv_eval (P : Bimodule A B C) (b : B) (c : C) :
    (moduleEvaluation A B b).map
      (X := ForgetEnrichment.of (Complex A) (P.rightAt c))
      (Y := ForgetEnrichment.of (Complex A)
        ((compose A B C C P (Bimodule.diagonal A C)).rightAt c)) (rightUnitIso A B C P c).inv =
      (rightUnitValueIso A B C P b c).inv :=
  moduleIsoMk_inv_eval A B _ _ b

/-- 右単位の比較は左Cの全Homにも自然。 -/
lemma rightUnitValue_left_naturality (P : Bimodule A B C) (b : B) (c c' : C) :
    (compose A B C C P (Bimodule.diagonal A C)).toFunctor.map c c' ≫
      moduleHomπ A B (rightAt A B C C P (Bimodule.diagonal A C) c)
        (rightAt A B C C P (Bimodule.diagonal A C) c') b ≫
      homPostcompose ((compose A B C C P (Bimodule.diagonal A C)).value b c)
        (rightUnitValueIso A B C P b c').hom =
    P.toFunctor.map c c' ≫ moduleHomπ A B (P.rightAt c) (P.rightAt c') b ≫
      homPrecompose (rightUnitValueIso A B C P b c).hom (P.value b c') := by
  change ((compose A B C C P (Bimodule.diagonal A C)).toFunctor.map c c' ≫
      moduleHomπ A B (rightAt A B C C P (Bimodule.diagonal A C) c)
        (rightAt A B C C P (Bimodule.diagonal A C) c') b) ≫
      homPostcompose (BalancedTensor.obj A C (representable A c) (P.leftAt b))
        (BalancedTensor.yonedaEvaluation A C c' (P.leftAt b)) =
    (P.leftAt b).map c c' ≫
      homPrecompose (BalancedTensor.yonedaEvaluation A C c (P.leftAt b)) (P.value b c')
  rw [compose_leftMap_π]
  change yonedaHom A C c c' ≫
      BalancedTensor.rightHomMap A C (representable A c) (representable A c') (P.leftAt b) ≫
        homPostcompose (BalancedTensor.obj A C (representable A c) (P.leftAt b))
          (BalancedTensor.yonedaEvaluation A C c' (P.leftAt b)) =
    (P.leftAt b).map c c' ≫
      homPrecompose (BalancedTensor.yonedaEvaluation A C c (P.leftAt b)) (P.value b c')
  exact BalancedTensor.yonedaEvaluation_representative_naturality A C (P.leftAt b) c c'

@[simp]
lemma rightUnitIso_hom_component (P : Bimodule A B C) (b : B) (c : C) :
    moduleMorphismComponent A B
      ((compose A B C C P (Bimodule.diagonal A C)).rightAt c) (P.rightAt c)
      (rightUnitIso A B C P c).hom b = (rightUnitValueIso A B C P b c).hom :=
  moduleIsoMk_hom_eval A B _ _ b

/-- 成分での自然性を右B加群の全Hom endの等式へ束ねる。 -/
lemma rightUnitIso_naturality (P : Bimodule A B C) (c c' : C) :
    (compose A B C C P (Bimodule.diagonal A C)).toFunctor.map c c' ≫
      moduleHomPostcompose A B
        ((compose A B C C P (Bimodule.diagonal A C)).rightAt c)
        ((compose A B C C P (Bimodule.diagonal A C)).rightAt c') (P.rightAt c')
        (rightUnitIso A B C P c').hom =
    P.toFunctor.map c c' ≫ moduleHomPrecompose A B
      ((compose A B C C P (Bimodule.diagonal A C)).rightAt c) (P.rightAt c) (P.rightAt c')
      (rightUnitIso A B C P c).hom := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  simp only [rightUnitIso_hom_component]
  exact rightUnitValue_left_naturality A B C P b c c'

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end RightUnit

/-! ## FubiniData（旧 SerrePositivity/DifferentialGraded/Tensor/FubiniData.lean） -/

/-! # Fubini比較の二つの反復tensorと三重生成元 -/

@[expose] public section FubiniData
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

/-- Q(c,e)⊗_C N(c)を値とする左E加群。 -/
def leftModule (Q : Bimodule A C E) (N : LeftModule A C) : LeftModule A E :=
  Q.toFunctor.comp (rightTensorDG A C N)

/-- R(e)⊗_E Q(c,e)を値とする右C加群。 -/
def rightModule (Q : Bimodule A C E) (R : RightModule A E) : RightModule A C :=
  Q.transposeDG.comp (leftTensorDG A E R)

/-- R⊗_E(Q⊗_C N)。 -/
def leftObj (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) : Complex A :=
  obj A E R (leftModule A C E Q N)

/-- (R⊗_E Q)⊗_C N。 -/
def rightObj (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) : Complex A :=
  obj A C (rightModule A C E Q R) N

/-- 三重tensorから左側の反復coendへの包含。 -/
def leftι (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) (c : C) (e : E) :
    R.obj (op e) ⊗ (Q.value c e ⊗ N.obj c) ⟶ leftObj A C E Q R N :=
  (R.obj (op e) ◁ ι A C (Q.rightAt e) N c) ≫ ι A E R (leftModule A C E Q N) e

/-- 同じ順序の三重tensorから右側の反復coendへの包含。 -/
def rightι (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) (c : C) (e : E) :
    R.obj (op e) ⊗ (Q.value c e ⊗ N.obj c) ⟶ rightObj A C E Q R N :=
  (α_ (R.obj (op e)) (Q.value c e) (N.obj c)).inv ≫
    (ι A E R (Q.leftAt c) e ▷ N.obj c) ≫ ι A C (rightModule A C E Q R) N c

/-- 左反復coendからの射は三重生成元で判定できる。 -/
lemma left_hom_ext (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C)
    {T : Complex A} {f g : leftObj A C E Q R N ⟶ T}
    (h : ∀ c e, leftι A C E Q R N c e ≫ f = leftι A C E Q R N c e ≫ g) : f = g := by
  apply hom_ext A E R (leftModule A C E Q N)
  intro e
  apply param_hom_ext A C (Q.rightAt e) N
  intro c
  exact h c e

/-- 右反復coendからの射も同じ順序の三重生成元で判定できる。 -/
lemma right_hom_ext (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C)
    {T : Complex A} {f g : rightObj A C E Q R N ⟶ T}
    (h : ∀ c e, rightι A C E Q R N c e ≫ f = rightι A C E Q R N c e ≫ g) : f = g := by
  apply hom_ext A C (rightModule A C E Q R) N
  intro c
  apply rightParam_hom_ext A E R (Q.leftAt c)
  intro e
  apply (cancel_epi (α_ (R.obj (op e)) (Q.value c e) (N.obj c)).inv).1
  simpa only [rightι, Category.assoc] using h c e

omit [Small.{u} E] in
/-- 左E作用を内側のC-coendの生成元で計算する。 -/
lemma leftModule_action_element (Q : Bimodule A C E) (N : LeftModule A C) (e e' : E) (c : C)
    {p r s a j n : ℤ} (ha : r + s = a) (hj : r + p = j) (hn : a + p = n)
    (f : GradedHom A e e' p) (q : (Q.value c e).X r) (v : (N.obj c).X s) :
    SerrePositivity.DifferentialGraded.leftAction A (leftModule A C E Q N) f
      (element A C (Q.rightAt e) N c q v ha) hn =
    element A C (Q.rightAt e') N c
      (SerrePositivity.DifferentialGraded.leftAction A (Q.leftAt c) f q hj) v (by omega) := by
  change (((rightHomMap A C (Q.rightAt e) (Q.rightAt e') N).f p
    ((Q.toFunctor.map e e').f p f)).v a n hn) (element A C (Q.rightAt e) N c q v ha) = _
  rw [rightHomMap_element_of_sum A C N (l := j) _ c q v ha (by omega) hn]
  rfl

end SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
end

end FubiniData

/-! ## FubiniFamilies（旧 SerrePositivity/DifferentialGraded/Tensor/FubiniFamilies.lean） -/

/-! # 二つの作用についてbalancedな三重tensor族の左反復coendへの降下 -/

@[expose] public section FubiniFamilies
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end FubiniFamilies

/-! ## FubiniRightAction（旧 SerrePositivity/DifferentialGraded/Tensor/FubiniRightAction.lean） -/

/-! # 右反復tensorの内側に誘導される右作用の符号 -/

@[expose] public section FubiniRightAction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

/-- 右C作用はRの次数とのKoszul符号を伴いQへ作用する。 -/
lemma rightModule_action_element (Q : Bimodule A C E) (R : RightModule A E)
    (c c' : Cᵒᵖ) (e : E) {p k r a j n : ℤ}
    (ha : k + r = a) (hj : r + p = j) (hn : a + p = n)
    (f : GradedHom A c c' p) (t : (R.obj (op e)).X k) (q : (Q.value c.unop e).X r) :
    moduleAction A (rightModule A C E Q R) f
      (element A E R (Q.leftAt c.unop) e t q ha) hn =
    (p * k).negOnePow • element A E R (Q.leftAt c'.unop) e t
      (moduleAction A (Q.rightAt e) f q hj) (by omega) := by
  change (((leftHomMap A E R (Q.leftAt c.unop) (Q.leftAt c'.unop)).f p
    ((Q.transposeHom c c').f p f)).v a n hn)
      (element A E R (Q.leftAt c.unop) e t q ha) = _
  have he := leftHomMap_element_of_sum A E R (l := j)
    ((Q.transposeHom c c').f p f) e t q ha (by omega) hn
  have h := congrArg (fun z => z.f p f) (Q.transposeHom_π c c' e)
  change (leftModuleHomπ A E (Q.leftAt c.unop) (Q.leftAt c'.unop) e).f p
      ((Q.transposeHom c c').f p f) = ((Q.rightAt e).map c c').f p f at h
  rw [h] at he
  exact he

end SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
end

end FubiniRightAction

/-! ## FubiniColumns（旧 SerrePositivity/DifferentialGraded/Tensor/FubiniColumns.lean） -/

/-! # 二重balanced族のE方向のパラメータ付き降下 -/

@[expose] public section FubiniColumns
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

omit [Small.{u} E] in
/-- 外側のbalanced関係を、内側の二つの和次数を明示して用いる。 -/
lemma DoubleFamily.balanceE_of_sums {Q : Bimodule A C E} {R : RightModule A E}
    {N : LeftModule A C} {T : Complex A} (a : DoubleFamily A C E Q R N T)
    (c : C) (e e' : E) {k p r s j i n : ℤ}
    (hj : r + p = j) (hi : j + s = i) (hn : k + p + (r + s) = n)
    (t : (R.obj (op e')).X k) (f : GradedHom A e e' p)
    (q : (Q.value c e).X r) (v : (N.obj c).X s) :
    (k * p).negOnePow • tripleElement A C E (n := n)
      (fun c e => (a.row e).val c) c e (moduleAction A R f t rfl) q v rfl (by omega) =
    tripleElement A C E (n := n) (fun c e => (a.row e).val c) c e' t
      (SerrePositivity.DifferentialGraded.leftAction A (Q.leftAt c) f q hj) v hi (by omega) := by
  subst j i
  exact a.balanceE c e e' k p r s n hn t f q v

/-- Cの対象を固定し、右にN(c)を置いたchain map族。 -/
def columnMaps {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) (c : C) (e : E) :
    (R.obj (op e) ⊗ Q.value c e) ⊗ N.obj c ⟶ T :=
  (α_ (R.obj (op e)) (Q.value c e) (N.obj c)).hom ≫ (a.row e).val c

omit [Small.{u} E] in
/-- N(c)を終域へ転置したE方向の族はbalancedである。 -/
def columnCurry {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) (c : C) :
    BalancedFamily A E R (Q.leftAt c) (homComplex A (N.obj c) T) := by
  refine balancedFamilyMk A E (fun e => curryRight (columnMaps A C E a c e)) ?_
  intro e e' k p r n hn t f q
  apply Cochain.ext
  intro s m hm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  rw [Cochain.units_smul_v]
  change (k * p).negOnePow •
    (columnMaps A C E a c e).f m
      (ιTensorObj (R.obj (op e) ⊗ Q.value c e) (N.obj c) n s m (by omega)
        (ιTensorObj (R.obj (op e)) (Q.value c e) (k + p) r n hn
          (moduleAction A R f t rfl ⊗ₜ[A] q) ⊗ₜ[A] v)) =
    (columnMaps A C E a c e').f m
      (ιTensorObj (R.obj (op e') ⊗ Q.value c e') (N.obj c) n s m (by omega)
        (ιTensorObj (R.obj (op e')) (Q.value c e') k (p + r) n (by omega)
          (t ⊗ₜ[A] SerrePositivity.DifferentialGraded.leftAction A (Q.leftAt c)
            (n := p + r) f q (by omega)) ⊗ₜ[A] v))
  simp only [columnMaps, comp_f, ModuleCat.comp_apply]
  rw [associator_apply_of_sums _ _ _ (k + p) r s n (r + s) m hn rfl (by omega),
    associator_apply_of_sums _ _ _ k (p + r) s n (p + r + s) m (by omega) rfl (by omega)]
  exact a.balanceE_of_sums A C E c e e' (j := p + r) (i := p + r + s)
    (by omega) rfl (by omega) t f q v

/-- 右パラメータ付き族のbalanced条件を転置から復元する。 -/
def columnFamily {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) (c : C) :
    RightParamFamily A E R (Q.leftAt c) (N.obj c) T := by
  refine ⟨columnMaps A C E a c, ?_⟩
  intro e e'
  apply (tensorRightHomEquiv (N.obj c) _ T).injective
  change curryRight (((rightAction A E R e e' ▷ (Q.leftAt c).obj e) ⊗ₘ 𝟙 (N.obj c)) ≫
    columnMaps A C E a c e) =
    curryRight ((((α_ (R.obj (op e')) (e ⟶[Complex A] e') ((Q.leftAt c).obj e)).hom ≫
      R.obj (op e') ◁ leftAction A E (Q.leftAt c) e e') ⊗ₘ 𝟙 (N.obj c)) ≫
        columnMaps A C E a c e')
  rw [curryRight_naturality_source, curryRight_naturality_source]
  exact (columnCurry A C E a c).property e e'

/-- 二重balanced族をEに関して降ろした射。 -/
def columnDesc {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) (c : C) :
    (rightModule A C E Q R).obj (op c) ⊗ N.obj c ⟶ T :=
  rightParamDesc A E R (Q.leftAt c) (columnFamily A C E a c)

@[reassoc (attr := simp)]
lemma ι_columnDesc {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) (c : C) (e : E) :
    (ι A E R (Q.leftAt c) e ▷ N.obj c) ≫ columnDesc A C E a c = columnMaps A C E a c e :=
  ι_rightParamDesc A E R (Q.leftAt c) (columnFamily A C E a c) e

/-- E方向の降下を斉次三重生成元で計算する。 -/
lemma columnDesc_element {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) (c : C) (e : E)
    {k r s l n : ℤ} (hl : k + r = l) (hn : l + s = n)
    (t : (R.obj (op e)).X k) (q : (Q.value c e).X r) (v : (N.obj c).X s) :
    (columnDesc A C E a c).f n
      (ιTensorObj ((rightModule A C E Q R).obj (op c)) (N.obj c) l s n hn
        (element A E R (Q.leftAt c) e t q hl ⊗ₜ[A] v)) =
    tripleElement A C E (fun c e => (a.row e).val c) c e t q v rfl (by omega) := by
  have h := rightParamDesc_element A E R (Q.leftAt c) (columnFamily A C E a c)
    e hl hn t q v
  change _ = (columnMaps A C E a c e).f n
    (ιTensorObj (R.obj (op e) ⊗ Q.value c e) (N.obj c) l s n hn
      (ιTensorObj (R.obj (op e)) (Q.value c e) k r l hl (t ⊗ₜ[A] q) ⊗ₜ[A] v)) at h
  simp only [columnMaps, comp_f, ModuleCat.comp_apply] at h
  rw [associator_apply_of_sum _ _ _ k r s l n hl hn] at h
  exact h

end SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
end

end FubiniColumns

/-! ## FubiniRightFamilies（旧 SerrePositivity/DifferentialGraded/Tensor/FubiniRightFamilies.lean） -/

/-! # 二重balanced族の右反復coendへの降下 -/

@[expose] public section FubiniRightFamilies
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

omit [Small.{u} E] in
/-- Cのbalanced関係を、外側tensorの二つの内側総次数を明示して適用する。 -/
lemma DoubleFamily.balanceC_of_sums {Q : Bimodule A C E} {R : RightModule A E}
    {N : LeftModule A C} {T : Complex A} (a : DoubleFamily A C E Q R N T)
    (c c' : C) (e : E) {k r p s i j n : ℤ}
    (hi : r + p + s = i) (hj : r + p + s = j) (hn : k + i = n)
    (t : (R.obj (op e)).X k) (q : (Q.value c' e).X r)
    (f : GradedHom A c c' p) (v : (N.obj c).X s) :
    (r * p).negOnePow • tripleElement A C E (n := n) (fun c e => (a.row e).val c)
      c e t (moduleAction A (Q.rightAt e) f q rfl) v hi hn =
    tripleElement A C E (i := j) (n := n) (fun c e => (a.row e).val c) c' e t q
      (SerrePositivity.DifferentialGraded.leftAction A N (n := p + s) f v (by omega))
      (by omega) (by omega) := by
  subst i j
  exact paramFamily_balanced_element A C (a.row e) c c' t q f v hn

/-- E方向に降ろした族はCのbalanced関係も保つ。 -/
lemma columnDesc_balanced_element {Q : Bimodule A C E} {R : RightModule A E}
    {N : LeftModule A C} {T : Complex A} (a : DoubleFamily A C E Q R N T)
    (c c' : C) (l p s n : ℤ) (hn : l + p + s = n)
    (z : ((rightModule A C E Q R).obj (op c')).X l) (f : GradedHom A c c' p)
    (v : (N.obj c).X s) :
    (l * p).negOnePow • familyElement A C (columnDesc A C E a) c
      (moduleAction A (rightModule A C E Q R) f z rfl) v hn =
    familyElement A C (columnDesc A C E a) c' z
      (SerrePositivity.DifferentialGraded.leftAction A N (n := p + s) f v (by omega))
      (by omega) := by
  let Z := rightModule A C E Q R
  let L : (Z.obj (op c')).X l →ₗ[A] T.X n :=
    ((l * p).negOnePow : ℤ) •
      ((columnDesc A C E a c).f n).hom.comp
        ((ιTensorObj (Z.obj (op c)) (N.obj c) (l + p) s n hn).hom.comp
          (((TensorProduct.mk A ((Z.obj (op c)).X (l + p)) ((N.obj c).X s)).flip v).comp
            ((((Z.map (op c') (op c)).f p f).v l (l + p) rfl).hom)))
  let H : (Z.obj (op c')).X l →ₗ[A] T.X n :=
    ((columnDesc A C E a c').f n).hom.comp
      ((ιTensorObj (Z.obj (op c')) (N.obj c') l (p + s) n (by omega)).hom.comp
        ((TensorProduct.mk A ((Z.obj (op c')).X l) ((N.obj c').X (p + s))).flip
          (SerrePositivity.DifferentialGraded.leftAction A N (n := p + s) f v (by omega))))
  have heq : ModuleCat.ofHom L = ModuleCat.ofHom H := by
    apply degree_element_ext A E R (Q.leftAt c')
    intro e k r hl t q
    change (l * p).negOnePow • (columnDesc A C E a c).f n
      (ιTensorObj (Z.obj (op c)) (N.obj c) (l + p) s n hn
        (moduleAction A Z f (element A E R (Q.leftAt c') e t q hl) rfl ⊗ₜ[A] v)) =
      (columnDesc A C E a c').f n
        (ιTensorObj (Z.obj (op c')) (N.obj c') l (p + s) n (by omega)
          (element A E R (Q.leftAt c') e t q hl ⊗ₜ[A]
            SerrePositivity.DifferentialGraded.leftAction A N (n := p + s) f v (by omega)))
    have hact := rightModule_action_element A C E Q R (op c') (op c) e
      (j := r + p) hl rfl (show l + p = l + p from rfl) f t q
    change moduleAction A Z f (element A E R (Q.leftAt c') e t q hl) rfl = _ at hact
    rw [hact]
    simp only [Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul]
    change (l * p).negOnePow • ((p * k).negOnePow •
      (columnDesc A C E a c).f n
        (ιTensorObj (Z.obj (op c)) (N.obj c) (l + p) s n hn
          (element A E R (Q.leftAt c) e t (moduleAction A (Q.rightAt e) f q rfl)
            (by omega) ⊗ₜ[A] v))) = _
    rw [columnDesc_element, columnDesc_element, smul_smul, ← Int.negOnePow_add]
    have hs : l * p + p * k = r * p + (k * p + k * p) := by
      rw [← hl]
      ring
    rw [hs, Int.negOnePow_add, Int.negOnePow_add, Int.units_mul_self, mul_one]
    exact a.balanceC_of_sums A C E c c' e (i := r + p + s) (j := r + (p + s))
      rfl (by omega) (by omega) t q f v
  exact congrArg (fun h => h z) heq

/-- 二重balanced族から右反復coendの外側へ渡すbalanced族。 -/
def rightFamily {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) :
    BalancedFamily A C (rightModule A C E Q R) N T :=
  balancedFamilyMk A C (columnDesc A C E a)
    (columnDesc_balanced_element A C E a)

/-- 二重balanced族の右反復coendへの降下。 -/
def rightDesc {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) : rightObj A C E Q R N ⟶ T :=
  desc A C (rightModule A C E Q R) N (rightFamily A C E a)

@[reassoc (attr := simp)]
lemma rightι_rightDesc {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) (c : C) (e : E) :
    rightι A C E Q R N c e ≫ rightDesc A C E a = (a.row e).val c := by
  change (α_ (R.obj (op e)) (Q.value c e) (N.obj c)).inv ≫
    (ι A E R (Q.leftAt c) e ▷ N.obj c) ≫ ι A C (rightModule A C E Q R) N c ≫
      desc A C (rightModule A C E Q R) N (rightFamily A C E a) = _
  rw [ι_desc]
  change (α_ (R.obj (op e)) (Q.value c e) (N.obj c)).inv ≫
    (ι A E R (Q.leftAt c) e ▷ N.obj c) ≫ columnDesc A C E a c = _
  rw [ι_columnDesc]
  simp only [columnMaps, Iso.inv_hom_id_assoc]

end SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
end

end FubiniRightFamilies

/-! ## FubiniRightRestriction（旧 SerrePositivity/DifferentialGraded/Tensor/FubiniRightRestriction.lean） -/

/-! # 右反復coendから二重balanced族への制限 -/

@[expose] public section FubiniRightRestriction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end FubiniRightRestriction

/-! ## Fubini（旧 SerrePositivity/DifferentialGraded/Tensor/Fubini.lean） -/

/-! # dg加群の相対tensorのFubini同型 -/

@[expose] public section Fubini
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

@[simp]
lemma leftRestrict_row_val {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (f : leftObj A C E Q R N ⟶ T) (c : C) (e : E) :
    ((leftRestrict A C E f).row e).val c = leftι A C E Q R N c e ≫ f := rfl

@[simp]
lemma rightRestrict_row_val {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (f : rightObj A C E Q R N ⟶ T) (c : C) (e : E) :
    ((rightRestrict A C E f).row e).val c = rightι A C E Q R N c e ≫ f := rfl

/-- R⊗_E(Q⊗_C N)≅(R⊗_E Q)⊗_C N。生成元の順をR,Q,Nに保つ。 -/
def iso (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) :
    leftObj A C E Q R N ≅ rightObj A C E Q R N where
  hom := leftDesc A C E (rightRestrict A C E (𝟙 (rightObj A C E Q R N)))
  inv := rightDesc A C E (leftRestrict A C E (𝟙 (leftObj A C E Q R N)))
  hom_inv_id := by
    apply left_hom_ext A C E Q R N
    intro c e
    simp only [leftι_leftDesc_assoc, rightRestrict_row_val, Category.comp_id,
      rightι_rightDesc, leftRestrict_row_val]
  inv_hom_id := by
    apply right_hom_ext A C E Q R N
    intro c e
    simp only [rightι_rightDesc_assoc, leftRestrict_row_val, Category.comp_id,
      leftι_leftDesc, rightRestrict_row_val]

@[reassoc (attr := simp)]
lemma leftι_iso_hom (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C)
    (c : C) (e : E) :
    leftι A C E Q R N c e ≫ (iso A C E Q R N).hom = rightι A C E Q R N c e := by
  simp only [iso, leftι_leftDesc, rightRestrict_row_val, Category.comp_id]

@[reassoc (attr := simp)]
lemma rightι_iso_inv (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C)
    (c : C) (e : E) :
    rightι A C E Q R N c e ≫ (iso A C E Q R N).inv = leftι A C E Q R N c e := by
  simp only [iso, rightι_rightDesc, leftRestrict_row_val, Category.comp_id]

/-- Fubini同型を通した降下は同じ二重balanced族の右降下に一致する。 -/
lemma iso_inv_leftDesc {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) :
    (iso A C E Q R N).inv ≫ leftDesc A C E a = rightDesc A C E a := by
  apply right_hom_ext A C E Q R N
  intro c e
  simp only [rightι_iso_inv_assoc, leftι_leftDesc, rightι_rightDesc]

lemma iso_hom_rightDesc {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) :
    (iso A C E Q R N).hom ≫ rightDesc A C E a = leftDesc A C E a := by
  apply left_hom_ext A C E Q R N
  intro c e
  simp only [leftι_iso_hom_assoc, rightι_rightDesc, leftι_leftDesc]

end SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
end

end Fubini
