module

public import SerrePositivity.InfinityCategories.F1.RightConeJoin

/-!
概要：prism の右錐と区間付き対角の右錐の比較の可換性。
方針：元の因子では対角の自然性、新しい頂点では prism の終端の式を使う。
規約：小さい標準単体を大きい標準単体の最後の面に含める。
使われ方：Kerodon Proposition 5.2.4.5、底の比較の pullback 正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：prism の右錐の比較は元の因子で底の最後の面の包含。
方針：時刻と係数の両射影で右錐の左包含の式を使う。
規約：時刻は恒等射で保つ。
使われ方：Kerodon Proposition 5.2.4.5、底の正方形の左因子での検査。 -/
lemma prismRightConeMap_inl (n : ℕ) :
    joinInl ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫ prismRightConeMap n =
      ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (Fin.last (n + 1))) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [prismRightConeMap, Category.assoc, lift_fst, ← Category.assoc, joinInl_joinMap,
      Category.assoc, relativeJoinConeTime_inl, Category.comp_id, whiskerLeft_fst]
  · rw [prismRightConeMap, Category.assoc, lift_snd, ← Category.assoc, joinInl_joinMap,
      Category.assoc, relativeJoinCone_stdSimplex_inl, whiskerLeft_snd]

/-- 概要：prism の右錐の新しい頂点は最後の係数の終端。
方針：時刻一と最後の係数の二成分を計算する。
規約：始域は標準零単体。
使われ方：Kerodon Proposition 5.2.4.5、底の正方形の新しい頂点での検査。 -/
lemma prismRightConeMap_inr (n : ℕ) :
    joinInr ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫ prismRightConeMap n =
      SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) ≫
        prismEndpoint 1 (Δ[n + 1] : SSet.{u}) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [prismRightConeMap, Category.assoc, lift_fst, ← Category.assoc, joinInr_joinMap,
      Category.id_comp, relativeJoinConeTime_inr, Category.assoc, prismEndpoint, lift_fst,
      SSet.comp_const]
  · rw [prismRightConeMap, Category.assoc, lift_snd, ← Category.assoc, joinInr_joinMap,
      Category.id_comp, relativeJoinCone_stdSimplex_inr, Category.assoc, prismEndpoint,
      lift_snd, Category.comp_id]

/-- 概要：対角の右錐は元の因子で右の係数だけを最後の面に含める。
方針：join の左包含と右因子の右錐の同型の式を使う。
規約：標的の左係数は小さい標準単体。
使われ方：Kerodon Proposition 5.2.4.5、対角の右錐の元の因子での計算。 -/
lemma prismRightConeDiagonal_inl (n : ℕ) :
    joinInl ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫ prismRightConeDiagonal n =
      joinDiagonal Δ[n] ≫ joinMap (𝟙 Δ[n]) (stdSimplex.δ (Fin.last (n + 1))) := by
  rw [prismRightConeDiagonal, ← Category.assoc, joinInl_joinMap, Category.assoc,
    rightConeJoinIso_inl]

/-- 概要：対角の右錐は新しい頂点を右側の最後の頂点へ写す。
方針：join の右包含と右因子の右錐の同型の式を使う。
規約：小さい左因子には新しい頂点を加えない。
使われ方：Kerodon Proposition 5.2.4.5、対角の右錐の新しい頂点の計算。 -/
lemma prismRightConeDiagonal_inr (n : ℕ) :
    joinInr ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫ prismRightConeDiagonal n =
      SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) ≫
        joinInr (Δ[n] : SSet.{u}) Δ[n + 1] := by
  rw [prismRightConeDiagonal, ← Category.assoc, joinInr_joinMap, Category.id_comp,
    rightConeJoinIso_inr]

/-- 概要：prism と対角の右錐の比較は大きい底の対角と可換。
方針：標準単体への射の等式を元の因子と新しい頂点で検査する。
規約：標的の左の最後の面の包含が正方形の右辺。
使われ方：Kerodon Proposition 5.2.4.5、底の比較の pullback 判定の可換条件。 -/
lemma prismRightCone_square (n : ℕ) :
    prismRightConeDiagonal.{u} n ≫ joinMap (stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]) =
      prismRightConeMap n ≫ joinDiagonal Δ[n + 1] := by
  have hL : joinInl ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫
      (prismRightConeDiagonal n ≫ joinMap (stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1])) =
      joinInl ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫ (prismRightConeMap n ≫ joinDiagonal Δ[n + 1]) := by
    rw [← Category.assoc, prismRightConeDiagonal_inl, Category.assoc, ← joinMap_comp,
      Category.id_comp, Category.comp_id, ← joinDiagonal_naturality,
      ← prismRightConeMap_inl, Category.assoc]
  have hR : joinInr ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫
      (prismRightConeDiagonal n ≫ joinMap (stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1])) =
      joinInr ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫ (prismRightConeMap n ≫ joinDiagonal Δ[n + 1]) := by
    rw [← Category.assoc, prismRightConeDiagonal_inr, Category.assoc, joinInr_joinMap,
      Category.id_comp, ← prismEndpoint_one_joinDiagonal, ← Category.assoc,
      ← prismRightConeMap_inr, Category.assoc]
  apply (cancel_mono (joinStdSimplexIso.{u} (n + 1) (n + 1)).hom).1
  apply relativeJoinCone_hom_ext_stdSimplex
  · simpa only [Category.assoc] using congrArg
      (fun k : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ join (Δ[n + 1] : SSet.{u}) Δ[n + 1] ↦
        k ≫ (joinStdSimplexIso (n + 1) (n + 1)).hom) hL
  · simpa only [Category.assoc] using congrArg
      (fun k : (Δ[0] : SSet.{u}) ⟶ join (Δ[n + 1] : SSet.{u}) Δ[n + 1] ↦
        k ≫ (joinStdSimplexIso (n + 1) (n + 1)).hom) hR

end SerrePositivity.InfinityCategories
