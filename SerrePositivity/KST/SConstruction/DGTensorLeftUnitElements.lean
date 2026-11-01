module
public import SerrePositivity.KST.SConstruction.DGComplexIsoEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import SerrePositivity.DifferentialGraded.Tensor.Triple
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions

public import SerrePositivity.DifferentialGraded.Tensor.Associator.Components

/-! # 実 tensor 左単位と結合の三重生成元計算
概要：左単位とその逆を、元の単位を挿入する生成元で計算する。
方針：元の単位同型を消去に使い、次数零の単位挿入を全次数の対象に適用する。
規約：balanced tensor の元を別の表示へ置換しない。使われ方：右恒等入力の Perf 単位法則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [Small.{u} B] [DGCategory A C] [Small.{u} C] [DGCategory A E]
  (P : Bimodule A B C) (Q : Bimodule A C E)

/-- 元の左単位を tensor に作用させた、各値の実同型。 -/
def dgTensorLeftUnitMapValueIso (b : B) (e : E) :
    (BimoduleTensor.compose A B C E
        (BimoduleTensor.compose A B B C (Bimodule.diagonal A B) P) Q).value b e ≅
      (BimoduleTensor.compose A B C E P Q).value b e where
  hom := BimoduleTensor.composeValueMap A B C E
    (BimoduleTensor.leftBimoduleUnitIso A B C P).hom
    (𝟙 (BimoduleCategory.of A C E Q)) b e
  inv := BimoduleTensor.composeValueMap A B C E
    (BimoduleTensor.leftBimoduleUnitIso A B C P).inv
    (𝟙 (BimoduleCategory.of A C E Q)) b e
  hom_inv_id := by
    have h := BimoduleTensor.composeValueMap_comp A B C E
      (BimoduleTensor.leftBimoduleUnitIso A B C P).hom
      (BimoduleTensor.leftBimoduleUnitIso A B C P).inv
      (𝟙 (BimoduleCategory.of A C E Q)) (𝟙 (BimoduleCategory.of A C E Q)) b e
    have hn := congrArg₂ (fun f g => BimoduleTensor.composeValueMap A B C E f g b e)
      (BimoduleTensor.leftBimoduleUnitIso A B C P).hom_inv_id
      (Category.id_comp (𝟙 (BimoduleCategory.of A C E Q)))
    exact h.symm.trans (hn.trans (BimoduleTensor.composeValueMap_id A B C E
      (BimoduleCategory.of A B C
        (BimoduleTensor.compose A B B C (Bimodule.diagonal A B) P))
      (BimoduleCategory.of A C E Q) b e))
  inv_hom_id := by
    have h := BimoduleTensor.composeValueMap_comp A B C E
      (BimoduleTensor.leftBimoduleUnitIso A B C P).inv
      (BimoduleTensor.leftBimoduleUnitIso A B C P).hom
      (𝟙 (BimoduleCategory.of A C E Q)) (𝟙 (BimoduleCategory.of A C E Q)) b e
    have hn := congrArg₂ (fun f g => BimoduleTensor.composeValueMap A B C E f g b e)
      (BimoduleTensor.leftBimoduleUnitIso A B C P).inv_hom_id
      (Category.id_comp (𝟙 (BimoduleCategory.of A C E Q)))
    exact h.symm.trans (hn.trans (BimoduleTensor.composeValueMap_id A B C E
      (BimoduleCategory.of A B C P) (BimoduleCategory.of A C E Q) b e))

/-- 元の左単位は、同じ対象に単位元を挿入した生成元を回収する。 -/
lemma dgTensorLeftUnit_hom_insert (M : RightModule A B) (b : B) (n : ℤ)
    (m : (M.obj (op b)).X n) :
    (BalancedTensor.leftUnitValueIso A B M b).hom.f n
        (BalancedTensor.element A B M ((Bimodule.diagonal A B).leftAt b) b
          m (unitElement A b).val (add_zero n)) = m := by
  rw [BalancedTensor.leftUnitValueIso_hom_element]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  exact moduleAction_unit A M (op b) n m

/-- 元の左 tensor 単位の逆射は、同じ対象の単位元を挿入する。 -/
lemma dgTensorLeftUnit_inv_insert (M : RightModule A B) (b : B) (n : ℤ)
    (m : (M.obj (op b)).X n) :
    (BalancedTensor.leftUnitValueIso A B M b).inv.f n m =
      BalancedTensor.element A B M ((Bimodule.diagonal A B).leftAt b) b
        m (unitElement A b).val (add_zero n) := by
  exact dgComplexIso_inv_apply_eq (BalancedTensor.leftUnitValueIso A B M b) n _ m
    (dgTensorLeftUnit_hom_insert A B M b n m)

/-- 各因子に作用させた左単位も、元の三重生成元を同じ右作用へ送る。 -/
lemma dgTensorLeftUnit_map_element (b x : B) (c : C) (e : E)
    {k r s i n : ℤ} (hi : r + s = i) (hn : k + i = n)
    (t : (Q.value c e).X k) (q : (P.value x c).X r) (f : GradedHom A b x s) :
    (BimoduleTensor.composeValueMap A B C E
        (BimoduleTensor.leftBimoduleUnitIso A B C P).hom
        (𝟙 (BimoduleCategory.of A C E Q)) b e).f n
        (BimoduleTensor.associatorLeftElement A B B C E (Bimodule.diagonal A B) P Q
          b x c e t q f hi hn) =
      (r * s).negOnePow • BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c t
        (moduleAction A (P.rightAt c) f q hi) hn := by
  have h := BimoduleTensor.composeValueMap_element A B C E
    (BimoduleTensor.leftBimoduleUnitIso A B C P).hom
    (𝟙 (BimoduleCategory.of A C E Q)) b c e t
    (BalancedTensor.element A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b) x q f hi) hn
  rw [(BimoduleCategory.valueEvaluation A C E c e).map_id,
    BimoduleTensor.leftBimoduleUnitIso_hom_value] at h
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply] at h
  dsimp only [BimoduleCategory.underlying, BimoduleCategory.of] at h
  have hu := BimoduleTensor.leftUnitValueIso_hom_element A B C P b x c q f hi
  refine h.trans ((congrArg (fun v : (P.value b c).X i =>
    BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c t v hn) hu).trans ?_)
  exact BalancedTensor.element_units_smul_right A C (Q.rightAt e) (P.leftAt b) c
    (r * s).negOnePow t (moduleAction A (P.rightAt c) f q hi) hn

/-- 左単位の逆を tensor へ作用させると、元の P 因子に単位元を挿入する。 -/
lemma dgTensorLeftUnit_inverse_map_element (b : B) (c : C) (e : E)
    {k r n : ℤ} (hn : k + r = n) (t : (Q.value c e).X k) (q : (P.value b c).X r) :
    (BimoduleTensor.composeValueMap A B C E
        (BimoduleTensor.leftBimoduleUnitIso A B C P).inv
        (𝟙 (BimoduleCategory.of A C E Q)) b e).f n
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c t q hn) =
      BimoduleTensor.associatorLeftElement A B B C E (Bimodule.diagonal A B) P Q
        b b c e t q (unitElement A b).val (add_zero r) hn := by
  have h := BimoduleTensor.composeValueMap_element A B C E
    (BimoduleTensor.leftBimoduleUnitIso A B C P).inv
    (𝟙 (BimoduleCategory.of A C E Q)) b c e t q hn
  rw [(BimoduleCategory.valueEvaluation A C E c e).map_id,
    BimoduleTensor.leftBimoduleUnitIso_inv_value] at h
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply] at h
  dsimp only [BimoduleCategory.underlying, BimoduleCategory.of] at h
  have hi := dgTensorLeftUnit_inv_insert A B (P.rightAt c) b r q
  refine h.trans (congrArg (fun v :
    (BalancedTensor.obj A B (P.rightAt c) ((Bimodule.diagonal A B).leftAt b)).X r =>
      BalancedTensor.element A C (Q.rightAt e)
        ((BimoduleTensor.compose A B B C (Bimodule.diagonal A B) P).leftAt b) c t v hn) hi)

/-- 元の双加群の値を保つ左単位の単位挿入公式。 -/
lemma dgBimoduleLeftUnit_hom_insert (R : Bimodule A B E) (b : B) (e : E) (n : ℤ)
    (m : (R.value b e).X n) :
    (BimoduleTensor.leftUnitValueIso A B E R b e).hom.f n
        (BalancedTensor.element A B (R.rightAt e) ((Bimodule.diagonal A B).leftAt b) b
          m (unitElement A b).val (add_zero n)) = m := by
  exact dgTensorLeftUnit_hom_insert A B (R.rightAt e) b n m

/-- 抽象的な balanced tensor の三つの射の合成を全次数の生成元で判定する。 -/
lemma dgBalancedTensor_triple_eq (M : RightModule A B) (N : LeftModule A B)
    {X Y V : Complex A} (f : BalancedTensor.obj A B M N ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ V) (j : BalancedTensor.obj A B M N ⟶ V)
    (hp : ∀ (b : B) (k r n : ℤ) (hn : k + r = n)
      (t : (M.obj (Opposite.op b)).X k) (q : (N.obj b).X r),
      h.f n (g.f n (f.f n (BalancedTensor.element A B M N b t q hn))) =
        j.f n (BalancedTensor.element A B M N b t q hn)) : f ≫ g ≫ h = j := by
  apply HomologicalComplex.hom_ext
  intro n
  apply BalancedTensor.degree_element_ext A B M N (V := V.X n)
  intro b k r hn t q
  exact (dgComplexMap_triple_apply f g h n
    (BalancedTensor.element A B M N b t q hn)).trans (hp b k r n hn t q)

/-- 源の複体の元の表示を保持して、balanced tensor の生成元判定を移送する。 -/
lemma dgBalancedTensor_triple_eq_of_source_eq (M : RightModule A B) (N : LeftModule A B)
    (V : Complex A) (e : V = BalancedTensor.obj A B M N)
    {X Y Z : Complex A} (f : V ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (j : V ⟶ Z)
    (hp : ∀ (b : B) (k r n : ℤ) (hn : k + r = n)
      (t : (M.obj (Opposite.op b)).X k) (q : (N.obj b).X r),
      h.f n (g.f n (f.f n ((eqToHom e.symm).f n
        (BalancedTensor.element A B M N b t q hn)))) =
      j.f n ((eqToHom e.symm).f n (BalancedTensor.element A B M N b t q hn))) :
    f ≫ g ≫ h = j := by
  subst V
  apply dgBalancedTensor_triple_eq A B M N
  intro b k r n hn t q
  simpa only [eqToHom_refl, HomologicalComplex.id_f, ModuleCat.id_apply] using
    hp b k r n hn t q

end SerrePositivity.KST.SConstruction
