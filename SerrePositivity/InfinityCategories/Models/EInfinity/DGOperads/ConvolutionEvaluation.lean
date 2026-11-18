module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorNaturality
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
模型。文献の定義との比較は後で
# Convolution の反復評価

概要：Berger–Fresse §3.1 の convolution で使う n 個の内部 Hom の同時評価を作る。
方針：右 tensor 転置の評価を n 回テンソルし、tensorμ で同じ位置の因子を合わせる。
規約：零入力の評価はテンソル単位の左単位子。
使われ方：P-coalgebra と P-algebra から Hom(H,B) の演算を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：内部 Hom を右 tensor 因子で評価する chain map（BF §3.1）。
方針：内部 Hom の恒等射を右 tensor 転置で戻す。
規約：引数の順序は Hom(H,B), H であり、余分な交換符号を加えない。
使われ方：convolution の n 重評価の一因子となる。 -/
def convolutionEvaluation (H B : Complex A) : homComplex A H B ⊗ H ⟶ B :=
  uncurryRight (𝟙 (homComplex A H B))

/-- 概要：右 tensor 評価は値域の chain map について自然（BF §3.1）。
方針：右 tensor 転置で射を比較し、後合成の自然性を使う。
規約：次数零だけでなく全複体の射の等式とする。
使われ方：convolution の後合成の関手性を証明する。 -/
@[reassoc]
lemma convolutionEvaluation_post (H : Complex A) {B B' : Complex A} (f : B ⟶ B') :
    (homPostcompose H f ▷ H) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation H B' =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation H B ≫ f := by
  apply (tensorRightHomEquiv H (homComplex A H B) B').injective
  change curryRight _ = curryRight _
  change curryRight ((homPostcompose H f ⊗ₘ 𝟙 H) ≫ _) = _
  rw [curryRight_naturality_source, curryRight_naturality_target]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation, curryRight_uncurryRight,
    Category.comp_id, Category.id_comp]

/-- 概要：右 tensor 評価は評価点の前合成について自然（BF §3.1）。
方針：右 tensor 転置の始域の自然性を使う。
規約：始域を変える射は次数を保つ chain map。
使われ方：端点・収縮による convolution の前合成を計算する。 -/
@[reassoc]
lemma convolutionEvaluation_pre {H H' : Complex A} (f : H' ⟶ H) (B : Complex A) :
    (homPrecompose f B ▷ H') ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation H' B =
      (homComplex A H B ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation H B := by
  apply (tensorRightHomEquiv H' (homComplex A H B) B).injective
  change curryRight _ = curryRight _
  change curryRight ((homPrecompose f B ⊗ₘ 𝟙 H') ≫ _) =
    curryRight ((𝟙 (homComplex A H B) ⊗ₘ f) ≫ _)
  rw [curryRight_naturality_source, curryRight_naturality_domain]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation, curryRight_uncurryRight,
    Category.comp_id, Category.id_comp]

/-- 概要：内部 Hom の n 重テンソルを n 個の点で同時評価する（BF §3.1）。
方針：先頭の評価と尾の反復評価を tensorμ で組み合わせる。
規約：n=0 を含み、交換は Koszul 対称性に従う。
使われ方：余演算の出力に各入力関数を適用する。 -/
def convolutionPowerEvaluation (H B : Complex A) : ∀ n : ℕ,
    power (homComplex A H B) n ⊗ power H n ⟶ power B n
  | 0 => (λ_ (𝟙_ (Complex A))).hom
  | n + 1 => tensorμ (homComplex A H B) (power (homComplex A H B) n) H (power H n) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation H B ⊗ₘ convolutionPowerEvaluation H B n)

/-- 概要：反復評価は値域の射について自然（BF §3.1）。
方針：一因子の自然性と tensorμ の自然性を帰納的に組み合わせる。
規約：出力には同じ射を全因子へ適用する。
使われ方：convolution の演算と代数射の後合成を両立させる。 -/
lemma convolutionPowerEvaluation_post (H : Complex A) {B B' : Complex A}
    (f : B ⟶ B') (n : ℕ) :
    (_root_.SerrePositivity.TensorPowers.map (homPostcompose H f) n ▷ power H n) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B' n =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B n ≫ _root_.SerrePositivity.TensorPowers.map f n := by
  induction n with
  | zero =>
    change (𝟙 (𝟙_ (Complex A)) ▷ (𝟙_ (Complex A))) ≫ (λ_ _).hom =
      (λ_ _).hom ≫ 𝟙 _
    simp only [id_whiskerRight, Category.id_comp, Category.comp_id]
  | succ n ih =>
    change ((homPostcompose H f ⊗ₘ _root_.SerrePositivity.TensorPowers.map (homPostcompose H f) n) ▷
      (H ⊗ power H n)) ≫
      (tensorμ _ _ _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation H B' ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B' n)) =
      (tensorμ _ _ _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation H B ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B n)) ≫ (f ⊗ₘ _root_.SerrePositivity.TensorPowers.map f n)
    rw [tensorμ_natural_left_assoc]
    simp only [Category.assoc, tensorHom_comp_tensorHom, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation_post, ih]


/-- 概要：反復評価は評価点の前合成について自然（BF §3.1）。
方針：一因子の前合成の自然性を tensorμ の左右の自然性で反復する。
規約：各出力点に同じ chain map を適用する。
使われ方：余代数射による convolution の前合成を代数射へ束ねる。 -/
lemma convolutionPowerEvaluation_pre {H H' : Complex A} (f : H' ⟶ H)
    (B : Complex A) (n : ℕ) :
    (_root_.SerrePositivity.TensorPowers.map (homPrecompose f B) n ▷ power H' n) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H' B n =
    (power (homComplex A H B) n ◁ _root_.SerrePositivity.TensorPowers.map f n) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B n := by
  induction n with
  | zero =>
    change (𝟙 (𝟙_ (Complex A)) ▷ (𝟙_ (Complex A))) ≫ (λ_ _).hom =
      ((𝟙_ (Complex A)) ◁ 𝟙 (𝟙_ (Complex A))) ≫ (λ_ _).hom
    simp only [id_whiskerRight, whiskerLeft_id]
  | succ n ih =>
    change ((homPrecompose f B ⊗ₘ _root_.SerrePositivity.TensorPowers.map (homPrecompose f B) n) ▷
      (H' ⊗ power H' n)) ≫
      (tensorμ _ _ _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation H' B ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H' B n)) =
      ((homComplex A H B ⊗ power (homComplex A H B) n) ◁
        (f ⊗ₘ _root_.SerrePositivity.TensorPowers.map f n)) ≫
      (tensorμ _ _ _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation H B ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B n))
    rw [tensorμ_natural_left_assoc, tensorμ_natural_right_assoc]
    simp only [tensorHom_comp_tensorHom, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation_pre, ih]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
