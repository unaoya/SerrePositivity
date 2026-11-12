module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutRightEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.LeftIntervalComparison

/-!
概要：左 Hom の最初の一頂点を、反転した path の最後の零頂点へ移す。
方針：有限順序の rev による path の像を取り、最小・最大の不等式を反転する。
規約：path の包含は反転せず、二端点の順序だけを反転する。
使われ方：混合 Hom の左端と反対 nerve の右 Hom 比較の接続。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories


/-- 頂点番号を反転し、二端点を交換した同じ path の像。 -/
def pathCutReverse {n : ℕ} {i j : Fin (n + 1)}
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) :
    Path (ULift.up j.rev : ULift.{u} (Fin (n + 1))) (ULift.up i.rev) where
  I := (fun k : ULift.{u} (Fin (n + 1)) => ULift.up k.down.rev) '' P.I
  left := ⟨ULift.up j, P.right, rfl⟩
  right := ⟨ULift.up i, P.left, rfl⟩
  left_le k hk := by
    obtain ⟨l, hl, rfl⟩ := hk
    exact Fin.rev_le_rev.mpr (P.le_right l hl)
  le_right k hk := by
    obtain ⟨l, hl, rfl⟩ := hk
    exact Fin.rev_le_rev.mpr (P.left_le l hl)

/-- 有限順序の path の反転は包含を保つ関手。 -/
def pathCutReverseFunctor {n : ℕ} (i j : Fin (n + 1)) :
    Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j) ⥤
      Path (ULift.up j.rev : ULift.{u} (Fin (n + 1))) (ULift.up i.rev) where
  obj := pathCutReverse
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩

/-- 実際の coherent な頂点反転の Hom 作用は、同じ path の反転の nerve。 -/
lemma coherentReverseThickening_map_pathCutReverse {n : ℕ} (i j : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentReverseThickening n).map
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ =
      nerveMap (pathCutReverseFunctor i j) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext (fun k => ?_)
  apply SimplicialThickening.Path.ext
  rfl

/-- 元の一ラベルは、頂点と時刻を反転すると零ラベルとなる。 -/
lemma pathCutReverseLabel_zero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {j : Fin (n + 1)} (hj : t j = 1) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom t j.rev = 0 := by
  change (t j.rev.rev).rev = 0
  rw [Fin.rev_rev, hj]
  rfl

/-- 元の零ラベルは、頂点と時刻を反転すると一ラベルとなる。 -/
lemma pathCutReverseLabel_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom t i.rev = 1 := by
  change (t i.rev.rev).rev = 1
  rw [Fin.rev_rev, hi]
  rfl

/-- 元の最初の一頂点の反転は、反転した path の最後の零頂点そのもの。 -/
lemma pathCutFirstOne_rev_eq_lastZero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hj : t j = 1)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom t) (pathCutReverseLabel_zero t hj)
      (pathCutReverse P) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hj P).rev := by
  apply le_antisymm
  · have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom t)
      (pathCutReverseLabel_zero t hj) (pathCutReverse P)
    obtain ⟨⟨k⟩, hk, he⟩ := hm.2
    have he' : k.rev = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom t)
        (pathCutReverseLabel_zero t hj) (pathCutReverse P) := congrArg ULift.down he
    have ht := hm.1
    rw [← he'] at ht
    change (t k.rev.rev).rev = 0 at ht
    rw [Fin.rev_rev] at ht
    have hk1 : t k = 1 := by
      have h := congrArg Fin.rev ht
      simpa only [Fin.rev_rev, show (0 : Fin 2).rev = 1 from rfl] using h
    rw [← he']
    exact Fin.rev_le_rev.mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_le t hj P k hk1 hk)
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutLastZero (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom t) (pathCutReverseLabel_zero t hj)
      (pathCutReverse P)
    · exact pathCutReverseLabel_zero t (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_spec t hj P).1
    · exact ⟨ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne t hj P), (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOne_spec t hj P).2, rfl⟩

/-- coherent 単体の反対の逆操作は、対象を反転した頂点の元の対象へ戻す。 -/
lemma coherentOppositeInverseSimplex_obj_reverse {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {n : ℕ} (F : (SimplicialNerve Cᵒᵖ) _⦋n⦌)
    (i : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeInverseSimplex F).obj ⟨ULift.up i⟩ =
      (F.obj ⟨ULift.up i.rev⟩).unop := rfl

/-- 反対の逆操作の Hom は、実際の path の反転に元の逆順の Hom 作用を続けた射。 -/
lemma coherentOppositeInverseSimplex_map_reverse {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {n : ℕ} (F : (SimplicialNerve Cᵒᵖ) _⦋n⦌)
    (i j : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeInverseSimplex F).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ =
      nerveMap (pathCutReverseFunctor i j) ≫
        F.map ⟨ULift.up j.rev⟩ ⟨ULift.up i.rev⟩ := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentReverseThickening n).map _ _ ≫ _) ≫ 𝟙 _ = _
  rw [Category.comp_id, coherentReverseThickening_map_pathCutReverse]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
