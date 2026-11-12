module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorBicone

/-!
# 二色テンソル語の自然性

## 概要
HA 3.2.4.7 の自由代数の指定比較に使う、二色の入力語の包含の自然性。

## 方針
入力ごとの射を語の各因子に適用し、二項直和の包含の自然性と再帰で比較する。

## 規約
語の添字を変えず、左右の色を保つ射だけを扱う。

## 使われ方
色付き Schur 分解を関手の比較へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.TensorPowers
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  {X Y X' Y' : C} [HasBinaryBiproduct X Y] [HasBinaryBiproduct X' Y']

/-- 色を保つ二つの射を、入力語の各テンソル因子へ適用する。 -/
def binaryTensorWordMap (f : X ⟶ X') (g : Y ⟶ Y') :
    ∀ n w, binaryTensorWordObj X Y n w ⟶ binaryTensorWordObj X' Y' n w
  | 0, _ => 𝟙 _
  | n + 1, .inl w => f ⊗ₘ binaryTensorWordMap f g n w
  | n + 1, .inr w => g ⊗ₘ binaryTensorWordMap f g n w

/-- 語ごとの射と、和のテンソル冪の射は指定包含の上で一致する。 -/
lemma binaryTensorWordInclusion_naturality (f : X ⟶ X') (g : Y ⟶ Y') :
    ∀ (n : ℕ) (w : BinaryTensorWord n),
    binaryTensorWordMap f g n w ≫ binaryTensorWordInclusion X' Y' n w =
      binaryTensorWordInclusion X Y n w ≫ TensorPowers.map (biprod.map f g) n := by
  intro n
  induction n with
  | zero => intro w; rfl
  | succ n ih =>
    intro w
    cases w with
    | inl w =>
      change (f ⊗ₘ binaryTensorWordMap f g n w) ≫ (biprod.inl ⊗ₘ _) =
        (biprod.inl ⊗ₘ _) ≫ (biprod.map f g ⊗ₘ _)
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, biprod.inl_map, ih]
    | inr w =>
      change (g ⊗ₘ binaryTensorWordMap f g n w) ≫ (biprod.inr ⊗ₘ _) =
        (biprod.inr ⊗ₘ _) ≫ (biprod.map f g ⊗ₘ _)
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, biprod.inr_map, ih]

/-- 語ごとの射と、和のテンソル冪の射は指定射影の上でも一致する。 -/
lemma binaryTensorWordProjection_naturality (f : X ⟶ X') (g : Y ⟶ Y') :
    ∀ (n : ℕ) (w : BinaryTensorWord n),
    TensorPowers.map (biprod.map f g) n ≫ binaryTensorWordProjection X' Y' n w =
      binaryTensorWordProjection X Y n w ≫ binaryTensorWordMap f g n w := by
  intro n
  induction n with
  | zero => intro w; rfl
  | succ n ih =>
    intro w
    cases w with
    | inl w =>
      change (biprod.map f g ⊗ₘ _) ≫ (biprod.fst ⊗ₘ _) =
        (biprod.fst ⊗ₘ _) ≫ (f ⊗ₘ binaryTensorWordMap f g n w)
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, biprod.map_fst, ih]
    | inr w =>
      change (biprod.map f g ⊗ₘ _) ≫ (biprod.snd ⊗ₘ _) =
        (biprod.snd ⊗ₘ _) ≫ (g ⊗ₘ binaryTensorWordMap f g n w)
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, biprod.map_snd, ih]

end SerrePositivity.EInfinity
