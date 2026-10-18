module

public import SerrePositivity.InfinityCategories.F1.RelativeJoinConeCoordinates
public import SerrePositivity.InfinityCategories.Stable.JoinAssociatorBoundary

/-!
概要：relative join の右錐から、大きい終域の通常の join への射。
方針：第一射影の右錐を join の結合同型で組み替え、右因子の錐を大きい標準単体にする。
規約：結合同型は既存の定義を読み取り専用で使う。
使われ方：Kerodon Proposition 5.2.4.5、relative join の右錐の比較の第一射影。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：relative join の右錐を、大きい標準単体との通常の join へ写す。
方針：第一射影を右錐に延ばしてから結合同型と標準単体の右錐の同型を合成する。
規約：始域の構造射は標準単体間の任意の射。
使われ方：Kerodon Proposition 5.2.4.5、右錐の比較を引き戻しへ持ち上げる第一成分。 -/
noncomputable def relativeJoinConeFirst {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    join (relativeJoin f (𝟙 Δ[n])) Δ[0] ⟶ join (Δ[m] : SSet.{u}) Δ[n + 1] :=
  joinMap (pullback.fst (joinMap f (𝟙 Δ[n])) (joinDiagonal Δ[n])) (𝟙 Δ[0]) ≫
    (stableJoinAssociator Δ[m] Δ[n] Δ[0]).hom ≫
      joinMap (𝟙 Δ[m]) (joinStdSimplexIso n 0).hom

/-- 概要：右錐の第一成分は元の relative join 上で終域の最後の面の包含を使う射。
方針：join の左包含と結合同型の可換性を計算する。
規約：左因子の標準単体は恒等射で保つ。
使われ方：Kerodon Proposition 5.2.4.5、小さい終域の比較との整合。 -/
lemma relativeJoinConeFirst_inl {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    joinInl (relativeJoin f (𝟙 Δ[n])) Δ[0] ≫ relativeJoinConeFirst f =
      pullback.fst (joinMap f (𝟙 Δ[n])) (joinDiagonal Δ[n]) ≫
        joinMap (𝟙 Δ[m]) (stdSimplex.δ (Fin.last (n + 1))) := by
  let q := pullback.fst (joinMap f (𝟙 Δ[n])) (joinDiagonal Δ[n])
  calc
    _ = q ≫ (joinInl (join (Δ[m] : SSet.{u}) Δ[n]) Δ[0] ≫
        (stableJoinAssociator Δ[m] Δ[n] Δ[0]).hom) ≫
          joinMap (𝟙 Δ[m]) (joinStdSimplexIso n 0).hom := by
      rw [relativeJoinConeFirst, ← Category.assoc, ← Category.assoc, joinInl_joinMap]
      simp only [q, Category.assoc]
    _ = q ≫ joinMap (𝟙 Δ[m]) (joinInl (Δ[n] : SSet.{u}) Δ[0]) ≫
        joinMap (𝟙 Δ[m]) (joinStdSimplexIso n 0).hom := by
      rw [stableJoinAssociator_inl]
    _ = _ := by
      rw [← joinMap_comp, Category.id_comp, relativeJoinCone_stdSimplex_inl]


/-- 概要：右錐の新しい頂点の第一成分は右因子の最後の頂点。
方針：結合同型が右端の因子を保つことと、標準単体の右錐の頂点の式を使う。
規約：新しい頂点の始域は標準零単体。
使われ方：Kerodon Proposition 5.2.4.5、右錐の比較の新しい頂点での整合。 -/
lemma relativeJoinConeFirst_inr {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    joinInr (relativeJoin f (𝟙 Δ[n])) Δ[0] ≫ relativeJoinConeFirst f =
      SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) ≫
        joinInr (Δ[m] : SSet.{u}) Δ[n + 1] := by
  rw [relativeJoinConeFirst, ← Category.assoc, ← Category.assoc, joinInr_joinMap,
    Category.id_comp, stableJoinAssociator_inr, Category.assoc, joinInr_joinMap,
    ← Category.assoc, relativeJoinCone_stdSimplex_inr]

/-- 概要：右錐の第一成分は単射。
方針：標準単体を底とする第一射影の単射性を、join と結合同型で保つ。
規約：終域の射や写像円柱の同値性を仮定しない。
使われ方：Kerodon Proposition 5.2.4.5、右錐の比較を部分複体として扱うための単射性。 -/
instance relativeJoinConeFirst_mono {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    Mono (relativeJoinConeFirst f) := by
  unfold relativeJoinConeFirst
  infer_instance

end SerrePositivity.InfinityCategories
