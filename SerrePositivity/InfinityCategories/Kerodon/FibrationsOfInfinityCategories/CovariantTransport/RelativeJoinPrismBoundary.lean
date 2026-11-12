module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinder
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinLeftFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinCylinderSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
概要：prism の零時刻の係数が最後の頂点を避ける場合の relative join の境界への因子化。
方針：join が読む先頭区間の単体が境界に入ることを示し、引き戻しの自然性で戻す。
規約：始域の係数は標準単体、終域は任意の単体集合。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、Z(m) の境界側への像の計算。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：切断より前の係数が最後の頂点を避ければ join の単体は左の境界から来る。
方針：非空の先頭区間の単体に最後の頂点がないことを境界の判定に使う。
規約：切断零では左の空単体をそのまま用いる。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、prism の境界への像の切断による計算。 -/
lemma join_prefix_mem_boundary {Y : SSet.{u}} {m d : ℕ} (c : Fin (d + 2))
    (a : (Δ[m] : SSet.{u}) _⦋d⦌) (b : Y _⦋d⦌)
    (h : ∀ i : Fin (d + 1), i.val < c.val → a i ≠ Fin.last m) :
    (⟨c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap Δ[m] (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl (d + 1) c.val
          (Nat.le_of_lt_succ c.isLt)) a,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap Y (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.suffixIncl (d + 1) c.val
          (Nat.le_of_lt_succ c.isLt)) b⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex Δ[m] Y d) ∈
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft (boundary m) Y).obj (Opposite.op ⦋d⦌) := by
  rcases c with ⟨l, hl⟩
  cases l with
  | zero =>
    refine ⟨⟨⟨0, hl⟩, PUnit.unit, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap Y (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.suffixIncl (d + 1) 0
      (Nat.le_of_lt_succ hl)) b⟩, ?_⟩
    rfl
  | succ l =>
    let x : (Δ[m] : SSet.{u}) _⦋l⦌ :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap Δ[m] (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl (d + 1) (l + 1)
        (Nat.le_of_lt_succ hl)) a
    have hx : x ∈ (boundary m).obj (Opposite.op ⦋l⦌) := by
      apply (mem_boundary_iff_notMem_range x).mpr
      refine ⟨Fin.last m, ?_⟩
      rintro ⟨i, hi⟩
      exact h (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl (d + 1) (l + 1) (Nat.le_of_lt_succ hl) i) i.isLt hi
    refine ⟨⟨⟨l + 1, hl⟩, ⟨x, hx⟩,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap Y (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.suffixIncl (d + 1) (l + 1)
        (Nat.le_of_lt_succ hl)) b⟩, ?_⟩
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ (by rfl) ?_ ?_
    · rfl
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id Y _ _

/-- 概要：relative join への prism の第一射影は二つの係数を持つ通常の join の円柱比較。
方針：対角円柱と join の誘導射の自然性を使う。
規約：右係数は元の係数を f で写したもの。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、prism の単体の切断による表示。 -/
lemma relativeJoinPrism_fst_app {X Y : SSet.{u}} (f : X ⟶ Y) (d : ℕ)
    (t : (Δ[1] : SSet.{u}) _⦋d⦌) (a : X _⦋d⦌) :
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y)).app (Opposite.op ⦋d⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f).app (Opposite.op ⦋d⦌) (t, a)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap X Y).app (Opposite.op ⦋d⦌) ((a, t), f.app _ a) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonalCylinder X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap (𝟙 X) f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap X Y := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_naturality]
  exact congrArg (fun k : (Δ[1] : SSet.{u}) ⊗ X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y ↦
    k.app (Opposite.op ⦋d⦌) (t, a)) he

/-- 概要：prism の零時刻に最後の頂点を取らない単体の比較像は境界の relative join に入る。
方針：左の join の境界への像を計算し、左因子の射の自然性の pullback で持ち上げる。
規約：終域 Y と構造射 f は任意。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、最後の prism セルより前の部分の因子化。 -/
lemma relativeJoinPrism_mem_boundary_of_no_last_zero {Y : SSet.{u}} {m d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) (t : (Δ[1] : SSet.{u}) _⦋d⦌)
    (a : (Δ[m] : SSet.{u}) _⦋d⦌)
    (h : ∀ i : Fin (d + 1), (t i).val = 0 → a i ≠ Fin.last m) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f).app (Opposite.op ⦋d⦌) (t, a) ∈ Set.range
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f)
        (boundary m).ι rfl).app
          (Opposite.op ⦋d⦌)) := by
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap_isPullback (𝟙 Y)
    (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl).app (Opposite.op ⦋d⦌)
  have hj : (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y)).app (Opposite.op ⦋d⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f).app (Opposite.op ⦋d⦌) (t, a)) ∈
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft (boundary m) Y).obj (Opposite.op ⦋d⦌) := by
    rw [relativeJoinPrism_fst_app, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_app]
    apply join_prefix_mem_boundary
    intro i hi
    apply h i
    have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff (stdSimplex.objEquiv t).toOrderHom 1 i).mp hi
    change (t i).val < 1 at he
    omega
  obtain ⟨b, hb⟩ := hj
  obtain ⟨z, hz, _⟩ := Types.exists_of_isPullback hp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f).app (Opposite.op ⦋d⦌) (t, a)) b hb.symm
  exact ⟨z, hz⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
