module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeNonjoint
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # 連結の元の非 joint 頂点の昇順列挙
概要：左右の非 joint 頂点の列挙を連結し、元の全頂点順序との順序同型を作る。
方針：二ブロック分解の全単射と、元の共有点での厳密な順序分離を使う。
規約：左から右への昇順。使われ方：右端数値座標と cube tensor の照合。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics


/-- 左右の元の昇順列挙を連結した全単射。 -/
def wedgeAscendingEquiv (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) :
    Fin (T.dimension + U.dimension) ≃ (T.wedge U).NonjointVertex :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr T.nonjointAscending.toEquiv U.nonjointAscending.toEquiv).trans
      (T.wedgeNonjointEquiv U))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeAscendingEquiv)


/-- 左ブロックの列挙は元の左の昇順列挙を回収する。 -/
lemma wedgeAscendingEquiv_left (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (i : Fin T.dimension) :
    T.wedgeAscendingEquiv U (Fin.castAdd U.dimension i) =
      T.wedgeNonjointLeft U (T.nonjointAscending i) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeAscendingEquiv, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd]
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeAscendingEquiv_left)


/-- 右ブロックの列挙は元の右の昇順列挙を回収する。 -/
lemma wedgeAscendingEquiv_right (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (i : Fin U.dimension) :
    T.wedgeAscendingEquiv U (Fin.natAdd T.dimension i) =
      T.wedgeNonjointRight U (U.nonjointAscending i) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeAscendingEquiv, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd]
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeAscendingEquiv_right)


/-- 元の昇順列挙の連結は、共有点を跨ぐ場合も厳密に順序を保つ。 -/
lemma wedgeAscendingEquiv_strictMono (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) :
    StrictMono (T.wedgeAscendingEquiv U) := by
  intro i j hij
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
  rcases a with a | a <;> rcases b with b | b
  · change a.val < b.val at hij
    change T.wedgeAscendingEquiv U (Fin.castAdd U.dimension a) <
      T.wedgeAscendingEquiv U (Fin.castAdd U.dimension b)
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeAscendingEquiv_left, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeAscendingEquiv_left]
    exact T.nonjointAscending.strictMono hij
  · change T.wedgeAscendingEquiv U (Fin.castAdd U.dimension a) <
      T.wedgeAscendingEquiv U (Fin.natAdd T.dimension b)
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeAscendingEquiv_left, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeAscendingEquiv_right]
    exact T.wedgeNonjointLeft_lt_right U _ _
  · change T.dimension + a.val < b.val at hij
    have := b.isLt
    omega
  · change T.dimension + a.val < T.dimension + b.val at hij
    change T.wedgeAscendingEquiv U (Fin.natAdd T.dimension a) <
      T.wedgeAscendingEquiv U (Fin.natAdd T.dimension b)
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeAscendingEquiv_right, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeAscendingEquiv_right]
    have hab := U.nonjointAscending.strictMono (show a < b by omega)
    change (U.nonjointAscending a).val.val < (U.nonjointAscending b).val.val at hab
    change T.vertexMax + (U.nonjointAscending a).val.val <
      T.vertexMax + (U.nonjointAscending b).val.val
    omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeAscendingEquiv_strictMono)


/-- 元の非 joint 頂点順序を保つ、左右の昇順列挙の連結。 -/
def wedgeAscendingIso (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) :
    Fin (T.dimension + U.dimension) ≃o (T.wedge U).NonjointVertex where
  toEquiv := T.wedgeAscendingEquiv U
  map_rel_iff' := (T.wedgeAscendingEquiv_strictMono U).le_iff_le

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeAscendingIso)


/-- 連結した昇順列挙は、元の necklace の昇順列挙と同じ番号を与える。 -/
lemma wedgeAscendingIso_index (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (i : Fin (T.dimension + U.dimension)) :
    ((T.wedge U).nonjointAscending.symm (T.wedgeAscendingIso U i)).val = i.val :=
  Fin.coe_orderIso_apply ((T.wedgeAscendingIso U).trans (T.wedge U).nonjointAscending.symm) i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeAscendingIso_index)


end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
