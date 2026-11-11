module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarGraded
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentDiagramVertexMap
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial

def dgCoherentBarPrefixOrder (n k : ℕ) (h : k ≤ n) : Fin (k + 1) →o Fin (n + 1) where
  toFun j := ⟨j.val, by omega⟩
  monotone' := fun _ _ hj => hj

def dgCoherentBarTailOrder (n k : ℕ) (h : k ≤ n) : Fin (n - k + 1) →o Fin (n + 1) where
  toFun j := ⟨k + j.val, by omega⟩
  monotone' := fun _ _ hj => Nat.add_le_add_left hj k

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarPrefix {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k ≤ n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I :=
  ⟨k, I.map (SimplexCategory.mkHom (dgCoherentBarPrefixOrder n k h)).op s⟩

def dgCoherentBarTail {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k ≤ n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I :=
  ⟨n - k, I.map (SimplexCategory.mkHom (dgCoherentBarTailOrder n k h)).op s⟩

lemma dgCoherentBarSource_prefix {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k ≤ n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (dgCoherentBarPrefix s k h) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩ := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex_map F _ s 0

lemma dgCoherentBarSource_tail {n : ℕ} (s : I _⦋n⦌) (k : ℕ) (h : k ≤ n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (dgCoherentBarTail s k h) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex F
        (I.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ ⟨k, by change k < n + 1; omega⟩).op s) := by
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex_map F (m := n - k) (n := n)
    (SimplexCategory.mkHom (dgCoherentBarTailOrder n k h)) s 0
  have hz : (SimplexCategory.mkHom (dgCoherentBarTailOrder n k h)).toOrderHom 0 =
      (⟨k, by omega⟩ : Fin (n + 1)) := Fin.ext (Nat.add_zero k)
  rw [hz] at hv
  exact hv

end SerrePositivity.InfinityCategories.Project.DerivedCategories
