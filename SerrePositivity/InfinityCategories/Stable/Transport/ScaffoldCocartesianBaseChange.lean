module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.RightFibration

/-!
分割で生成：docstring を書き直すこと
 # 元の cocartesian 切断の分類と、実底変換の指定点を同じ scaffold 復元で比較する
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

private lemma recoverPoint {C : Type*} [Category C] {a b z : C}
    (e : a ≅ b) (x : z ⟶ a) (y : z ⟶ b) (h : x ≫ e.hom = y) :
    y ≫ e.inv = x := by
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private lemma appendPoint {C : Type*} [Category C] {a b c d e : C}
    (x : a ⟶ b) (y : b ⟶ c) (f : c ⟶ d) (z : a ⟶ d) (g : d ⟶ e)
    (h : x ≫ y ≫ f = z) : x ≫ y ≫ f ≫ g = z ≫ g := by
  simpa only [Category.assoc] using congrArg (fun m => m ≫ g) h

variable {I : Type u} [Category.{u} I] {E B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [LeftFibration p] (k : nerve I ⟶ B)

local instance instLeftFibrationSndSSet_4 : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

end SerrePositivity.KST.Fibration
