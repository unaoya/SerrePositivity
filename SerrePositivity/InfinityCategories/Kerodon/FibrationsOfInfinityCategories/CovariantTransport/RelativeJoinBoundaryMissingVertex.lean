module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinPrismBoundary

/-!
概要：境界 relative join に入る prism の単体で欠ける左の係数頂点。
方針：境界の左単体で欠ける頂点を取り、join の切断より前の区間へ移す。
規約：零時刻の全頂点で同じ係数頂点が欠けることを結論する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、Z(m) が境界の逆像全体であることの検査。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：左の境界との join の単体には左区間で欠ける係数頂点がある。
方針：境界の単体が欠ける頂点を使い、空区間では任意の頂点を取る。
規約：左区間の単体は空区間を補った標準単体の順序写像で読む。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、prism の境界への逆像の切断による計算。 -/
lemma join_left_boundary_exists_missing_vertex {Y : SSet.{u}} {m d : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[m] : SSet.{u}) Y d)
    (hs : s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft (boundary m) Y).obj (Opposite.op ⦋d⦌)) :
    ∃ v : Fin (m + 1), ∀ i : Fin s.1.val, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv m _ s.2.1) i ≠ v := by
  obtain ⟨⟨⟨l, hl⟩, a, b⟩, rfl⟩ := hs
  cases l with
  | zero =>
    refine ⟨0, ?_⟩
    intro i
    exact Fin.elim0 i
  | succ l =>
    change (boundary m : SSet.{u}) _⦋l⦌ at a
    obtain ⟨v, hv⟩ := (mem_boundary_iff_notMem_range a.val).mp a.property
    refine ⟨v, ?_⟩
    intro i hi
    exact hv ⟨i, hi⟩

/-- 概要：円柱比較の像が左の境界との join に入れば零時刻の係数に欠ける頂点がある。
方針：切断より前の頂点がちょうど零時刻であることを使って欠ける頂点を戻す。
規約：同じ欠ける頂点を全ての零時刻の頂点で使う。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、最後の prism セルでの境界の検査。 -/
lemma joinCylinderMap_left_boundary_exists_missing_vertex {Y : SSet.{u}} {m d : ℕ}
    (a : (Δ[m] : SSet.{u}) _⦋d⦌) (t : (Δ[1] : SSet.{u}) _⦋d⦌) (b : Y _⦋d⦌)
    (hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[m] Y).app (Opposite.op ⦋d⦌) ((a, t), b) ∈
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft (boundary m) Y).obj (Opposite.op ⦋d⦌)) :
    ∃ v : Fin (m + 1), ∀ i : Fin (d + 1), (t i).val = 0 → a i ≠ v := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_app] at hs
  obtain ⟨v, hv⟩ := join_left_boundary_exists_missing_vertex _ hs
  refine ⟨v, ?_⟩
  intro i hi
  let c := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋d⦌) t).1
  have hic : i.val < c.val := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff (stdSimplex.objEquiv t).toOrderHom 1 i).mpr
    change (t i).val < 1
    omega
  have he := hv ⟨i.val, hic⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv m c.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap Δ[m]
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.prefixIncl (d + 1) c.val (Nat.le_of_lt_succ c.isLt)) a)) ⟨i.val, hic⟩ ≠ v at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv_augMap] at he
  exact he

/-- 概要：prism の比較像が境界 relative join に入れば零時刻の係数に欠ける頂点がある。
方針：左因子の自然な射の第一射影の式で通常の join の境界へ写し、その欠ける頂点を使う。
規約：構造射 f の終域は任意の単体集合。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、境界 relative join の逆像の必要条件。 -/
lemma relativeJoinPrism_boundary_exists_missing_vertex {Y : SSet.{u}} {m d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) (t : (Δ[1] : SSet.{u}) _⦋d⦌)
    (a : (Δ[m] : SSet.{u}) _⦋d⦌)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f).app (Opposite.op ⦋d⦌) (t, a) ∈ Set.range
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f)
        (boundary m).ι rfl).app (Opposite.op ⦋d⦌))) :
    ∃ v : Fin (m + 1), ∀ i : Fin (d + 1), (t i).val = 0 → a i ≠ v := by
  obtain ⟨z, hz⟩ := h
  apply joinCylinderMap_left_boundary_exists_missing_vertex a t (f.app _ a)
  refine ⟨(pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap ((boundary m).ι ≫ f) (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y)).app _ z, ?_⟩
  have he := congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin ((boundary m).ι ≫ f) (𝟙 Y) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[m] : SSet.{u}) Y ↦ k.app (Opposite.op ⦋d⦌) z)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap_fst (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl)
  have he' := congrArg (fun x ↦
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y)).app (Opposite.op ⦋d⦌) x) hz
  exact he.symm.trans (he'.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_fst_app f d t a))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
