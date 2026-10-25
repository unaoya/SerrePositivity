module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarGraded
public import SerrePositivity.InfinityCategories.DGNerve.CoherentDiagramVertexMap
/-!
概要：元の coherent dg 図式の prefix と tail の単体ラベルと端点を保持する。
方針：切断番号を加える順序写像と、始点を保つ順序写像を明示する。
規約：高次単体と端点の厳密な比較を保持し、普通の合成図式には置き換えない。
使われ方：coherent bar 微分の各 prefix 成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial

def dgCoherentBarPrefixOrder (n k : ℕ) (h : k ≤ n) : Fin (k + 1) →o Fin (n + 1) where
  toFun j := ⟨j.val, by omega⟩
  monotone' := fun _ _ hj => hj

def dgCoherentBarTailOrder (n k : ℕ) (h : k ≤ n) : Fin (n - k + 1) →o Fin (n + 1) where
  toFun j := ⟨k + j.val, by omega⟩
  monotone' := fun _ _ hj => Nat.add_le_add_left hj k

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarPrefix {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k ≤ n) :
    dgCoherentBarIndex I :=
  ⟨k, I.map (SimplexCategory.mkHom (dgCoherentBarPrefixOrder n k h)).op s⟩

def dgCoherentBarTail {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k ≤ n) :
    dgCoherentBarIndex I :=
  ⟨n - k, I.map (SimplexCategory.mkHom (dgCoherentBarTailOrder n k h)).op s⟩

lemma dgCoherentBarSource_prefix {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k ≤ n) :
    dgCoherentBarSource R D F (dgCoherentBarPrefix s k h) =
      dgCoherentBarSource R D F ⟨n, s⟩ := by
  exact coherentDiagramVertex_map F _ s 0

lemma dgCoherentBarSource_tail {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k ≤ n) :
    dgCoherentBarSource R D F (dgCoherentBarTail s k h) =
      coherentDiagramVertex F
        (I.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ ⟨k, by change k < n + 1; omega⟩).op s) := by
  have hv := coherentDiagramVertex_map F (m := n - k) (n := n)
    (SimplexCategory.mkHom (dgCoherentBarTailOrder n k h)) s 0
  have hz : (SimplexCategory.mkHom (dgCoherentBarTailOrder n k h)).toOrderHom 0 =
      (⟨k, by omega⟩ : Fin (n + 1)) := Fin.ext (Nat.add_zero k)
  rw [hz] at hv
  exact hv

end SerrePositivity.InfinityCategories
