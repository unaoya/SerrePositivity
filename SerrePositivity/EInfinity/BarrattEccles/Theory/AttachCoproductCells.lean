module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# 余積の包含に沿うセル付加

## 概要
Berger–Moerdijk 命題 4.1 の次数付きセル付加では、disk が境界と生成元の余積に分かれる。

## 方針
実際の付加の pushout と各 disk の余積性から、先行段と新しい生成元の余積を構成する。

## 規約
指定された余錐の脚を保つ。

## 使われ方
微分を消したセル代数の後続段の自由表示。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

namespace SerrePositivity.EInfinity

open CategoryTheory Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] {I : Type t} {S D G : I → C}
  {g : ∀ i, S i ⟶ D i} {X Y : C} {f : X ⟶ Y}
  (c : AttachCells.{w} g f) (j : ∀ i, G i ⟶ D i)

/-- Preserving the defining coproducts and pushout preserves the cell attachment. -/
def mapAttachCells {D' : Type u} [Category.{v} D'] (F : C ⥤ D')
    [PreservesColimitsOfShape (Discrete c.ι) F] [PreservesColimitsOfShape WalkingSpan F] :
    AttachCells.{w} (fun i => F.map (g i)) (F.map f) where
  ι := c.ι
  π := c.π
  cofan₁ := Cofan.mk (F.obj c.cofan₁.pt) (fun i => F.map (c.cofan₁.inj i))
  cofan₂ := Cofan.mk (F.obj c.cofan₂.pt) (fun i => F.map (c.cofan₂.inj i))
  isColimit₁ := isColimitCofanMkObjOfIsColimit _ _ _ (c.isColimit₁.ofIsoColimit
    (Cofan.ext (Iso.refl _) (fun i => by simp)))
  isColimit₂ := isColimitCofanMkObjOfIsColimit _ _ _ (c.isColimit₂.ofIsoColimit
    (Cofan.ext (Iso.refl _) (fun i => by simp)))
  m := F.map c.m
  hm i := by
    change F.map (c.cofan₁.inj i) ≫ F.map c.m =
      F.map (g (c.π i)) ≫ F.map (c.cofan₂.inj i)
    rw [← F.map_comp, ← F.map_comp, c.hm]
  g₁ := F.map c.g₁
  g₂ := F.map c.g₂
  isPushout := c.isPushout.map F

/-- The cocone of the old object and the free complements of the attached cells. -/
def attachComplementCofan : Cofan (fun i : Option c.ι =>
    i.elim X (fun k => G (c.π k))) :=
  Cofan.mk Y (fun i => match i with
    | none => f
    | some k => j (c.π k) ≫ c.cell k)

/-- Attaching along the left coproduct inclusions freely adds the other summands. -/
def attachComplementIsColimit
    (h : ∀ i, IsColimit (BinaryCofan.mk (g i) (j i))) :
    IsColimit (attachComplementCofan c j) := by
  let V := fun i : Option c.ι => i.elim X (fun k => G (c.π k))
  let diskMap (s : Cofan V) (i : c.ι) :=
    BinaryCofan.IsColimit.desc (h (c.π i)) ((c.cofan₁.inj i ≫ c.g₁) ≫ s.inj none)
      (s.inj (some i))
  let dc (s : Cofan V) := Cofan.mk s.pt (diskMap s)
  let d (s : Cofan V) := c.isColimit₂.desc (dc s)
  have hd (s : Cofan V) (i : c.ι) : c.cofan₂.inj i ≫ d s = diskMap s i :=
    c.isColimit₂.fac (dc s) (Discrete.mk i)
  have hL (s : Cofan V) (i : c.ι) : g (c.π i) ≫ diskMap s i =
      (c.cofan₁.inj i ≫ c.g₁) ≫ s.inj none :=
    BinaryCofan.IsColimit.inl_desc (h (c.π i)) _ _
  have hR (s : Cofan V) (i : c.ι) : j (c.π i) ≫ diskMap s i = s.inj (some i) :=
    BinaryCofan.IsColimit.inr_desc (h (c.π i)) _ _
  have hw (s : Cofan V) : c.g₁ ≫ s.inj none = c.m ≫ d s := by
    apply Cofan.IsColimit.hom_ext c.isColimit₁
    intro i
    rw [← Category.assoc (c.cofan₁.inj i) c.m, c.hm i, Category.assoc, hd, hL,
      Category.assoc]
  let desc (s : Cofan V) := c.isPushout.desc (s.inj none) (d s) (hw s)
  have h₀ (s : Cofan V) : f ≫ desc s = s.inj none := c.isPushout.inl_desc _ _ _
  have hcell (s : Cofan V) (i : c.ι) : c.cell i ≫ desc s = diskMap s i := by
    dsimp only [AttachCells.cell_def, desc]
    rw [Category.assoc, c.isPushout.inr_desc, hd]
  have hn (s : Cofan V) (i : c.ι) : (j (c.π i) ≫ c.cell i) ≫ desc s = s.inj (some i) := by
    rw [Category.assoc, hcell, hR]
  refine Cofan.IsColimit.mk _ desc (fun s i => ?_) ?_
  · cases i with
    | none => exact h₀ s
    | some i => exact hn s i
  · intro s k hk
    change Y ⟶ s.pt at k
    have hk₀ : f ≫ k = s.inj none := hk none
    apply c.hom_ext (hk₀.trans (h₀ s).symm)
    intro i
    apply BinaryCofan.IsColimit.hom_ext (h (c.π i))
    · change g (c.π i) ≫ c.cell i ≫ k = g (c.π i) ≫ c.cell i ≫ desc s
      have hi : g (c.π i) ≫ c.cell i = (c.cofan₁.inj i ≫ c.g₁) ≫ f := by
        rw [AttachCells.cell_def, ← c.hm_assoc, ← c.isPushout.w, Category.assoc]
      rw [← Category.assoc (g (c.π i)) (c.cell i) k,
        ← Category.assoc (g (c.π i)) (c.cell i) (desc s), hi]
      simp only [Category.assoc, hk₀, h₀]
    · change j (c.π i) ≫ c.cell i ≫ k = j (c.π i) ≫ c.cell i ≫ desc s
      rw [← Category.assoc, ← Category.assoc]
      exact (hk (some i)).trans (hn s i).symm

end SerrePositivity.EInfinity
