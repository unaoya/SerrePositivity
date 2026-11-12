module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarIndexMap
public import Mathlib.Order.LatticeIntervals

/-!
概要：共通上界を持つ poset の単体を、その上界以下の部分圏へ持ち上げる。
方針：各頂点を同じ要素の subtype とし、poset の射の一意性を使う。
規約：元の単体と始点係数を保持する。
使われ方：filtered な bar の有限 cycle を終頂点のある部分へ移す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {J : Type u} [PartialOrder J]

def dgHomologyBarLowerInclusion (b : J) : Set.Iic b ⥤ J :=
  (show Set.Iic b →o J from ⟨Subtype.val, fun _ _ h => h⟩).monotone.functor

def dgHomologyBarLiftSimplex {n : ℕ} (s : (nerve J) _⦋n⦌) (b : J)
    (hb : s.obj (Fin.last n) ≤ b) : (nerve (Set.Iic b)) _⦋n⦌ :=
  (show Fin (n + 1) →o Set.Iic b from
    ⟨fun i => ⟨s.obj i, (s.monotone (Fin.le_last i)).trans hb⟩,
      fun _ _ h => s.monotone h⟩).monotone.functor

lemma dgHomologyBarLiftSimplex_comp {n : ℕ} (s : (nerve J) _⦋n⦌) (b : J)
    (hb : s.obj (Fin.last n) ≤ b) :
    dgHomologyBarLiftSimplex s b hb ⋙ dgHomologyBarLowerInclusion b = s := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

lemma dgHomologyBarLowerInclusion_simplex_injective (b : J) (n : ℕ) :
    Function.Injective (fun s : (nerve (Set.Iic b)) _⦋n⦌ =>
      s ⋙ dgHomologyBarLowerInclusion b) := by
  intro s t h
  apply CategoryTheory.Functor.ext
    (fun i => Subtype.ext (congrArg (fun f => f.obj i) h))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
