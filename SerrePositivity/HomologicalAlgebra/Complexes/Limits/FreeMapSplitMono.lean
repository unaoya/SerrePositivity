module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# 単射の自由加群像の実分裂

概要：集合の単射を自由加群化した射は分裂単射。
方針：像の生成元を元の生成元へ戻し、像の外を零へ送る。
規約：空の始域を含み、集合での retraction の存在は仮定しない。
使われ方：正規化単体の境界の各次数での分裂。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
variable (A : Type u) [CommRing A]

def freeMapRetraction {X Y : Type u} (f : X ⟶ Y) :
    (ModuleCat.free A).obj Y ⟶ (ModuleCat.free A).obj X := by
  classical
  exact ModuleCat.freeDesc (↾fun y => if h : ∃ x, f x = y then ModuleCat.freeMk h.choose else 0)

lemma freeMap_isSplitMono {X Y : Type u} (f : X ⟶ Y) (hf : Function.Injective f) :
    IsSplitMono ((ModuleCat.free A).map f) := by
  classical
  refine ⟨⟨{ retraction := _root_.SerrePositivity.ComplexLimits.freeMapRetraction A f, id := ?_ }⟩⟩
  apply ModuleCat.free_hom_ext
  intro x
  change _root_.SerrePositivity.ComplexLimits.freeMapRetraction A f ((ModuleCat.free A).map f (ModuleCat.freeMk x)) = _
  rw [ModuleCat.free_map_apply]
  change ModuleCat.freeDesc _ (ModuleCat.freeMk (f x)) = ModuleCat.freeMk x
  rw [ModuleCat.freeDesc_apply]
  change (if h : ∃ y, f y = f x then ModuleCat.freeMk h.choose else 0) = ModuleCat.freeMk x
  rw [dite_eq_left (show ∃ y, f y = f x from ⟨x, rfl⟩)]
  congr 1
  exact hf (Exists.choose_spec (show ∃ y, f y = f x from ⟨x, rfl⟩))

end SerrePositivity.ComplexLimits
