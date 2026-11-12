module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinConeCoordinates

/-!
概要：relative join の右錐から大きい底の区間付き係数への射。
方針：時刻は新しい頂点を一に送り、係数は標準単体の右錐の同型で延長する。
規約：区間は左因子。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、右錐の比較の引き戻しの第二成分。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：relative join の右錐を大きい底の区間付き係数へ写す。
方針：元の射影の時刻と係数を別々に右錐へ延長して直積へまとめる。
規約：新しい頂点は時刻一、係数は最後の頂点。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、右錐の比較の底上の条件。 -/
noncomputable def relativeJoinConeSecond {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Δ[n])) Δ[0] ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Δ[n])) (𝟙 Δ[0]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeTime)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[n])) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n]) ≫
      snd (Δ[1] : SSet.{u}) Δ[n]) (𝟙 Δ[0]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom)

/-- 概要：右錐の第二成分は元の因子で最後の面の包含による底の変更に一致する。
方針：時刻と係数の二つの射影で、それぞれの右錐の左包含の式を使う。
規約：時刻は保ち、係数だけを最後の面に含める。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、小さい底の relative join の比較との整合。 -/
lemma relativeJoinConeSecond_inl {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Δ[n])) Δ[0] ≫ relativeJoinConeSecond f =
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[n])) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n]) ≫
        ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (Fin.last (n + 1))) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [relativeJoinConeSecond, Category.assoc, lift_fst, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeTime_inl, Category.comp_id,
      Category.assoc, whiskerLeft_fst]
    rfl
  · rw [relativeJoinConeSecond, Category.assoc, lift_snd, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCone_stdSimplex_inl]
    simp only [Category.assoc, whiskerLeft_snd]

/-- 概要：右錐の新しい頂点の第二成分は最後の係数の prism の終端。
方針：新しい頂点の時刻が一で係数が最後であることを直積の両射影で確認する。
規約：始域は標準零単体。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、右錐の比較の新しい頂点での底の整合。 -/
lemma relativeJoinConeSecond_inr {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Δ[n])) Δ[0] ≫ relativeJoinConeSecond f =
      SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[n + 1] : SSet.{u}) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [relativeJoinConeSecond, Category.assoc, lift_fst, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap,
      Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeTime_inr, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_fst,
      SSet.comp_const]
  · rw [relativeJoinConeSecond, Category.assoc, lift_snd, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap,
      Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCone_stdSimplex_inr, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint,
      lift_snd, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
