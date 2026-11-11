module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RightConeJoin

/-!
概要：prism の右錐と区間付き対角の右錐の比較の可換性。
方針：元の因子では対角の自然性、新しい頂点では prism の終端の式を使う。
規約：小さい標準単体を大きい標準単体の最後の面に含める。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、底の比較の pullback 正方形。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：prism の右錐の比較は元の因子で底の最後の面の包含。
方針：時刻と係数の両射影で右錐の左包含の式を使う。
規約：時刻は恒等射で保つ。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、底の正方形の左因子での検査。 -/
lemma prismRightConeMap_inl (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeMap n =
      ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (Fin.last (n + 1))) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeMap, Category.assoc, lift_fst, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeTime_inl, Category.comp_id, whiskerLeft_fst]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeMap, Category.assoc, lift_snd, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCone_stdSimplex_inl, whiskerLeft_snd]

/-- 概要：prism の右錐の新しい頂点は最後の係数の終端。
方針：時刻一と最後の係数の二成分を計算する。
規約：始域は標準零単体。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、底の正方形の新しい頂点での検査。 -/
lemma prismRightConeMap_inr (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeMap n =
      SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[n + 1] : SSet.{u}) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeMap, Category.assoc, lift_fst, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap,
      Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinConeTime_inr, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_fst,
      SSet.comp_const]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeMap, Category.assoc, lift_snd, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap,
      Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCone_stdSimplex_inr, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint,
      lift_snd, Category.comp_id]

/-- 概要：対角の右錐は元の因子で右の係数だけを最後の面に含める。
方針：join の左包含と右因子の右錐の同型の式を使う。
規約：標的の左係数は小さい標準単体。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、対角の右錐の元の因子での計算。 -/
lemma prismRightConeDiagonal_inl (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeDiagonal n =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[n]) (stdSimplex.δ (Fin.last (n + 1))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeDiagonal, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.rightConeJoinIso_inl]

/-- 概要：対角の右錐は新しい頂点を右側の最後の頂点へ写す。
方針：join の右包含と右因子の右錐の同型の式を使う。
規約：小さい左因子には新しい頂点を加えない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、対角の右錐の新しい頂点の計算。 -/
lemma prismRightConeDiagonal_inr (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeDiagonal n =
      SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[n + 1] := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeDiagonal, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.rightConeJoinIso_inr]

/-- 概要：prism と対角の右錐の比較は大きい底の対角と可換。
方針：標準単体への射の等式を元の因子と新しい頂点で検査する。
規約：標的の左の最後の面の包含が正方形の右辺。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、底の比較の pullback 判定の可換条件。 -/
lemma prismRightCone_square (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeDiagonal.{u} n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeMap n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n + 1] := by
  have hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeDiagonal n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1])) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeMap n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n + 1]) := by
    rw [← Category.assoc, prismRightConeDiagonal_inl, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
      Category.id_comp, Category.comp_id, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_naturality,
      ← prismRightConeMap_inl, Category.assoc]
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeDiagonal n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1])) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismRightConeMap n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n + 1]) := by
    rw [← Category.assoc, prismRightConeDiagonal_inr, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap,
      Category.id_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_one_joinDiagonal, ← Category.assoc,
      ← prismRightConeMap_inr, Category.assoc]
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} (n + 1) (n + 1)).hom).1
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCone_hom_ext_stdSimplex
  · simpa only [Category.assoc] using congrArg
      (fun k : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n + 1] : SSet.{u}) Δ[n + 1] ↦
        k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) (n + 1)).hom) hL
  · simpa only [Category.assoc] using congrArg
      (fun k : (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n + 1] : SSet.{u}) Δ[n + 1] ↦
        k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) (n + 1)).hom) hR

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
