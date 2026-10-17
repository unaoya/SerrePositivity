module
public import SerrePositivity.DifferentialGraded.Tensor.KFlatComplex
public import Mathlib.Logic.Small.List

/-! # 複体値quiverの非空有限pathのtensor項

内部頂点のリストで非空pathを表す。空リストは一辺、恒等pathは別の添字で扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v)

/-- 合成・単位をまだ持たない複体値quiver。 -/
abbrev ComplexQuiver := D → D → Complex A

/-- 非空path x→b₁→…→bᵣ→yの内部微分を持つ全次数tensor。 -/
def wordTensor (K : ComplexQuiver A D) : List D → D → D → Complex A
  | [], x, y => K x y
  | b :: w, x, y => K x b ⊗ wordTensor K w b y

/-- 辺ごとのchain mapを有限pathのtensorに延長する。 -/
def wordMap {K L : ComplexQuiver A D} (f : ∀ x y, K x y ⟶ L x y) :
    ∀ (w : List D) (x y : D), wordTensor A D K w x y ⟶ wordTensor A D L w x y
  | [], x, y => f x y
  | b :: w, x, y => f x b ⊗ₘ wordMap f w b y

lemma wordMap_id (K : ComplexQuiver A D) (w : List D) (x y : D) :
    wordMap A D (fun x y => 𝟙 (K x y)) w x y = 𝟙 (wordTensor A D K w x y) := by
  induction w generalizing x with
  | nil => rfl
  | cons b w ih =>
    change (𝟙 (K x b)) ⊗ₘ wordMap A D (fun x y => 𝟙 (K x y)) w b y = _
    rw [ih, id_tensorHom_id]
    rfl

lemma wordMap_comp {K L M : ComplexQuiver A D}
    (f : ∀ x y, K x y ⟶ L x y) (g : ∀ x y, L x y ⟶ M x y)
    (w : List D) (x y : D) :
    wordMap A D (fun x y => f x y ≫ g x y) w x y =
      wordMap A D f w x y ≫ wordMap A D g w x y := by
  induction w generalizing x with
  | nil => rfl
  | cons b w ih =>
    change (f x b ≫ g x b) ⊗ₘ wordMap A D (fun x y => f x y ≫ g x y) w b y =
      (f x b ⊗ₘ wordMap A D f w b y) ≫ (g x b ⊗ₘ wordMap A D g w b y)
    rw [ih, tensorHom_comp_tensorHom]

/-- 有限pathのtensor項のK-flat性。次数や有界性の制約は置かない。 -/
lemma wordTensor_kFlat (K : ComplexQuiver A D) (hK : ∀ x y, complexKFlat A (K x y))
    (w : List D) (x y : D) : complexKFlat A (wordTensor A D K w x y) := by
  induction w generalizing x with
  | nil => exact hK x y
  | cons b w ih => exact complexKFlat_tensor A (hK x b) (ih b)

/-- 非空pathの連結。接続頂点yを内部頂点として加える。 -/
def concatenate (w z : List D) (y : D) : List D := w ++ y :: z

/-- 連結したpath項のtensor括弧を比較する。 -/
def wordConcatenationIso (K : ComplexQuiver A D) :
    ∀ (w z : List D) (x y t : D),
      wordTensor A D K w x y ⊗ wordTensor A D K z y t ≅
        wordTensor A D K (concatenate D w z y) x t
  | [], _, _, _, _ => Iso.refl _
  | b :: w, z, x, y, t =>
    (α_ (K x b) (wordTensor A D K w b y) (wordTensor A D K z y t)) ≪≫
      (tensorLeft (K x b)).mapIso (wordConcatenationIso K w z b y t)

end SerrePositivity.DifferentialGraded.FreeDGCategory
