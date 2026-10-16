module
public import SerrePositivity.DifferentialGraded.Category.Examples
public import SerrePositivity.DifferentialGraded.Complexes.Cells
public import SerrePositivity.DifferentialGraded.Module.Colimits
public import Mathlib.Logic.Small.List

/-! # 明示的dg商の有限pathとtensor項

中間対象は指定full部分圏Sに属する。各中間対象に次数−1の記号を一つ置く。
ここでの複体は各tensor項の内部微分のみを持つ。dε=idによる長さを下げる項は後続で追加する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- pathの収縮記号を置く中間対象の有限語。空語も許す。 -/
abbrev Word {D : Type v} (S : Set D) := List S

/-- 各中間対象に対応する収縮記号の合計次数。 -/
def epsilonDegree {D : Type v} {S : Set D} (w : Word S) : ℤ := -(w.length : ℤ)

@[simp] lemma epsilonDegree_nil {D : Type v} (S : Set D) :
    epsilonDegree ([] : Word S) = 0 := rfl

@[simp] lemma epsilonDegree_cons {D : Type v} {S : Set D} (b : S) (w : Word S) :
    epsilonDegree (b :: w) = epsilonDegree w - 1 := by
  simp [epsilonDegree]
  omega

lemma epsilonDegree_append {D : Type v} {S : Set D} (w z : Word S) :
    epsilonDegree (w ++ z) = epsilonDegree w + epsilonDegree z := by
  dsimp [epsilonDegree]
  rw [List.length_append, Nat.cast_add]
  abel

/-- 収縮記号を表す次数−1のA複体。内部微分は零である。 -/
abbrev epsilonComplex : Complex A := complexSphere A (-1)

/-- path x→b₁→…→bᵣ→yの全次数tensor項。元のHomの次数を制限しない。 -/
def term {S : Set D} : Word S → D → D → Complex A
  | [], x, y => homObject A D x y
  | b :: w, x, y => homObject A D x b.val ⊗ (epsilonComplex A ⊗ term w b.val y)

@[simp] lemma term_nil (S : Set D) (x y : D) :
    term A D ([] : Word S) x y = homObject A D x y := rfl

@[simp] lemma term_cons {S : Set D} (b : S) (w : Word S) (x y : D) :
    term A D (b :: w) x y = homObject A D x b.val ⊗
      (epsilonComplex A ⊗ term A D w b.val y) := rfl

/-- 単一の収縮記号を持つpath項への、実際の次数−1生成射。 -/
def epsilonTerm {S : Set D} (b : S) : epsilonComplex A ⟶ term A D [b] b.val b.val :=
  (λ_ (epsilonComplex A)).inv ≫
    (eId (Complex A) b.val ⊗ₘ
      ((ρ_ (epsilonComplex A)).inv ≫ (𝟙 (epsilonComplex A) ⊗ₘ eId (Complex A) b.val)))

variable [Small.{u} D]

instance wordSmall (S : Set D) : Small.{u} (Word S) := inferInstanceAs (Small.{u} (List S))

/-- 全有限path項の直和。ここでは内部微分だけを持つ補助複体。 -/
abbrev internalHom (S : Set D) (x y : D) : Complex A := ∐ (fun w : Word S => term A D w x y)

/-- 指定path項から全path直和への包含。 -/
def ι (S : Set D) (x y : D) (w : Word S) : term A D w x y ⟶ internalHom A D S x y :=
  Sigma.ι (fun w : Word S => term A D w x y) w

/-- 空pathの包含。後続の最終微分でも元のdg Homの包含となる。 -/
def originalHom (S : Set D) (x y : D) : homObject A D x y ⟶ internalHom A D S x y :=
  ι A D S x y []

/-- 指定対象bの次数−1記号を全path直和へ入れる。まだ収縮の方程式は主張しない。 -/
def epsilon (S : Set D) (b : S) : epsilonComplex A ⟶ internalHom A D S b.val b.val :=
  epsilonTerm A D b ≫ ι A D S b.val b.val [b]

/-- path直和からの射は各有限path項上で決まる。 -/
lemma hom_ext (S : Set D) (x y : D) {T : Complex A} (f g : internalHom A D S x y ⟶ T)
    (h : ∀ w : Word S, ι A D S x y w ≫ f = ι A D S x y w ≫ g) : f = g :=
  Sigma.hom_ext f g h

end SerrePositivity.DifferentialGraded.DGQuotient
