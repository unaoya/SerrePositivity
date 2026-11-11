module
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.SequentialProduct

/-!
概要：可算列の先頭へ一段加えても、その cocone と余極限を保つ。
方針：cocone を tail に制限し、元の余極限普遍性を使う。
規約：任意の圏の既存の余極限だけを使う。
使われ方：D-8 d の disk 初期段を二つの sphere 層へ分解する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits
variable {C : Type u} [Category.{v} C] {X : ℕ → C} (f : ∀ n, X n ⟶ X (n + 1))
  {B : C} (b : B ⟶ X 0)

def dgKappaPrependObject : ℕ → C
  | 0 => B
  | n + 1 => X n

def dgKappaPrependTransition : ∀ n,
    dgKappaPrependObject (X := X) (B := B) n ⟶
      dgKappaPrependObject (X := X) (B := B) (n + 1)
  | 0 => b
  | n + 1 => f n

def dgKappaPrependTailCocone
    (c : Cocone (Functor.ofSequence (dgKappaPrependTransition f b))) :
    Cocone (Functor.ofSequence f) where
  pt := c.pt
  ι := NatTrans.ofSequence (fun n => c.ι.app (n + 1)) (by
    intro n
    have h := c.w (homOfLE (Nat.le_succ (n + 1)))
    simp only [Functor.ofSequence_map_homOfLE_succ, dgKappaPrependTransition] at h ⊢
    exact h.trans (Category.comp_id _).symm)

def dgKappaPrependCocone (c : Cocone (Functor.ofSequence f)) :
    Cocone (Functor.ofSequence (dgKappaPrependTransition f b)) where
  pt := c.pt
  ι := NatTrans.ofSequence
    (fun n => match n with | 0 => b ≫ c.ι.app 0 | n + 1 => c.ι.app n) (by
      intro n
      cases n with
      | zero =>
        simp only [Functor.ofSequence_map_homOfLE_succ, dgKappaPrependTransition]
        exact (Category.comp_id _).symm
      | succ n =>
        have h := c.w (homOfLE (Nat.le_succ n))
        simp only [Functor.ofSequence_map_homOfLE_succ, dgKappaPrependTransition] at h ⊢
        exact h.trans (Category.comp_id _).symm)

def dgKappaPrependIsColimit {c : Cocone (Functor.ofSequence f)} (hc : IsColimit c) :
    IsColimit (dgKappaPrependCocone f b c) where
  desc t := hc.desc (dgKappaPrependTailCocone f b t)
  fac t n := by
    cases n with
    | zero =>
      change (b ≫ c.ι.app 0) ≫ hc.desc (dgKappaPrependTailCocone f b t) = t.ι.app 0
      rw [Category.assoc, hc.fac]
      have h := t.w (homOfLE (Nat.le_succ 0))
      simpa only [Functor.ofSequence_map_homOfLE_succ, dgKappaPrependTransition] using! h
    | succ n => exact hc.fac (dgKappaPrependTailCocone f b t) n
  uniq t a h := by
    apply hc.hom_ext
    intro n
    exact (h (n + 1)).trans (hc.fac (dgKappaPrependTailCocone f b t) n).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
