module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：相対 latching と pushout-product の交換に現れる二つの反復 pushout。
方針：同じ三つの外側の頂点への射と三つの整合式によって両者の普遍性を記述する。
規約：任意の pushout を持つ圏の通常の余極限の計算。
使われ方：Goerss–Jardine VII §4。Reedy anodyne な重みの射と境界の相対 tensor。
-/

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Spectra.PushoutCube
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {A B X A' B' X' Y : C}
  {u : A ⟶ B} {l : A ⟶ X} {a : A ⟶ A'} {b : B ⟶ B'} {x : X ⟶ X'}
  {u' : A' ⟶ B'} {l' : A' ⟶ X'} {m : B ⟶ Y} {t : X ⟶ Y}

/-- 二つの平行な pushout の間の、実際の可換正方形による射。 -/
abbrev upperMap (hb : u ≫ b = a ≫ u') (hx : l ≫ x = a ≫ l') :
    pushout u l ⟶ pushout u' l' := pushout.map u l u' l' b x a hb hx

/-- 前面の pushout から外側の頂点への射。 -/
abbrev diagonalMap (hy : u ≫ m = l ≫ t) : pushout u l ⟶ Y := pushout.desc m t hy

/-- 中央の pushout から別の前面の pushout への射の整合式。 -/
lemma middle_condition (hx : l ≫ x = a ≫ l') (hy : u ≫ m = l ≫ t) :
    a ≫ (l' ≫ pushout.inl x t) = u ≫ (m ≫ pushout.inr x t) := by
  rw [← Category.assoc, ← hx, Category.assoc, pushout.condition,
    ← Category.assoc, ← hy, Category.assoc]

/-- 中央の pushout から、右の頂点への射。 -/
abbrev middleLeft (hb : u ≫ b = a ≫ u') : pushout a u ⟶ B' :=
  pushout.desc u' b hb.symm

/-- 中央の pushout から、後面の pushout への射。 -/
abbrev middleRight (hx : l ≫ x = a ≫ l') (hy : u ≫ m = l ≫ t) :
    pushout a u ⟶ pushout x t :=
  pushout.desc (l' ≫ pushout.inl x t) (m ≫ pushout.inr x t) (middle_condition hx hy)

/-- 先に平行な二面の pushout を取る側。 -/
abbrev rightObj (hb : u ≫ b = a ≫ u') (hx : l ≫ x = a ≫ l') (hy : u ≫ m = l ≫ t) :=
  pushout (upperMap hb hx) (diagonalMap hy)

/-- 先に交差する二面の pushout を取る側。 -/
abbrev leftObj (hb : u ≫ b = a ≫ u') (hx : l ≫ x = a ≫ l') (hy : u ≫ m = l ≫ t) :=
  pushout (middleLeft hb) (middleRight hx hy)

variable (hb : u ≫ b = a ≫ u') (hx : l ≫ x = a ≫ l') (hy : u ≫ m = l ≫ t)

abbrev rightB : B' ⟶ rightObj hb hx hy :=
  pushout.inl u' l' ≫ pushout.inl (upperMap hb hx) (diagonalMap hy)
abbrev rightX : X' ⟶ rightObj hb hx hy :=
  pushout.inr u' l' ≫ pushout.inl (upperMap hb hx) (diagonalMap hy)
abbrev rightY : Y ⟶ rightObj hb hx hy := pushout.inr (upperMap hb hx) (diagonalMap hy)
abbrev leftB : B' ⟶ leftObj hb hx hy := pushout.inl (middleLeft hb) (middleRight hx hy)
abbrev leftX : X' ⟶ leftObj hb hx hy :=
  pushout.inl x t ≫ pushout.inr (middleLeft hb) (middleRight hx hy)
abbrev leftY : Y ⟶ leftObj hb hx hy :=
  pushout.inr x t ≫ pushout.inr (middleLeft hb) (middleRight hx hy)

lemma right_condition_A : u' ≫ rightB hb hx hy = l' ≫ rightX hb hx hy := by
  simp only [rightB, rightX, ← Category.assoc, pushout.condition]
lemma right_condition_B : b ≫ rightB hb hx hy = m ≫ rightY hb hx hy := by
  have h := congrArg (fun f ↦ pushout.inl u l ≫ f)
    (pushout.condition (f := upperMap hb hx) (g := diagonalMap hy))
  simpa only [upperMap, diagonalMap, pushout.inl_desc_assoc,
    Category.assoc, pushout.inl_desc] using h
lemma right_condition_X : x ≫ rightX hb hx hy = t ≫ rightY hb hx hy := by
  have h := congrArg (fun f ↦ pushout.inr u l ≫ f)
    (pushout.condition (f := upperMap hb hx) (g := diagonalMap hy))
  simpa only [upperMap, diagonalMap, pushout.inr_desc_assoc,
    Category.assoc, pushout.inr_desc] using h
lemma left_condition_A : u' ≫ leftB hb hx hy = l' ≫ leftX hb hx hy := by
  have h := congrArg (fun f ↦ pushout.inl a u ≫ f)
    (pushout.condition (f := middleLeft hb) (g := middleRight hx hy))
  simpa only [middleLeft, middleRight, pushout.inl_desc_assoc,
    Category.assoc, pushout.inl_desc] using h
lemma left_condition_B : b ≫ leftB hb hx hy = m ≫ leftY hb hx hy := by
  have h := congrArg (fun f ↦ pushout.inr a u ≫ f)
    (pushout.condition (f := middleLeft hb) (g := middleRight hx hy))
  simpa only [middleLeft, middleRight, pushout.inr_desc_assoc,
    Category.assoc, pushout.inr_desc] using h
lemma left_condition_X : x ≫ leftX hb hx hy = t ≫ leftY hb hx hy := by
  simp only [leftX, leftY, ← Category.assoc, pushout.condition]

variable {T : C} (fB : B' ⟶ T) (fX : X' ⟶ T) (fY : Y ⟶ T)
  (hA : u' ≫ fB = l' ≫ fX) (hB : b ≫ fB = m ≫ fY) (hX : x ≫ fX = t ≫ fY)

/-- 三つの外側の射から平行二面側への普遍的な射を作る。 -/
def rightDesc : rightObj hb hx hy ⟶ T :=
  pushout.desc (pushout.desc fB fX hA) fY (by
    apply pushout.hom_ext
    · simp only [upperMap, diagonalMap, pushout.inl_desc_assoc,
        Category.assoc, pushout.inl_desc]
      exact hB
    · simp only [upperMap, diagonalMap, pushout.inr_desc_assoc,
        Category.assoc, pushout.inr_desc]
      exact hX)

/-- 同じ三つの外側の射から交差二面側への普遍的な射を作る。 -/
def leftDesc : leftObj hb hx hy ⟶ T :=
  pushout.desc fB (pushout.desc fX fY hX) (by
    apply pushout.hom_ext
    · simp only [middleLeft, middleRight, pushout.inl_desc_assoc,
        Category.assoc, pushout.inl_desc]
      exact hA
    · simp only [middleLeft, middleRight, pushout.inr_desc_assoc,
        Category.assoc, pushout.inr_desc]
      exact hB)

end
end SerrePositivity.KST.Spectra.PushoutCube
