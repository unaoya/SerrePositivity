module

public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinConeMap
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinIdentity
public import SerrePositivity.InfinityCategories.Core.JoinLeftColimits

/-!
概要：標準単体の prism の右錐から大きい標準単体の prism への比較。
方針：時刻と係数を右錐へ延長し、relative join の第二成分の因子化として扱う。
規約：新しい係数頂点の時刻は一。
使われ方：Kerodon Proposition 5.2.4.5、右錐の比較の引き戻しによる全射性の検査。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：標準単体の prism の右錐を一つ大きい prism へ写す。
方針：時刻を区間の右錐から戻し、係数を標準単体の右錐の同型で写す。
規約：新しい右頂点は時刻一と最後の係数頂点へ写る。
使われ方：Kerodon Proposition 5.2.4.5、右錐の底の座標の比較。 -/
noncomputable def prismRightConeMap (n : ℕ) :
    join ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] :=
  lift (joinMap (fst (Δ[1] : SSet.{u}) Δ[n]) (𝟙 Δ[0]) ≫ relativeJoinConeTime)
    (joinMap (snd (Δ[1] : SSet.{u}) Δ[n]) (𝟙 Δ[0]) ≫ (joinStdSimplexIso n 0).hom)

/-- 概要：relative join の右錐の第二成分は prism の右錐の比較を経由する。
方針：直積の両射影で join の合成則を使う。
規約：右錐へ延ばす射は元の relative join の第二射影。
使われ方：Kerodon Proposition 5.2.4.5、右錐の比較の pullback の組み合わせ。 -/
lemma relativeJoinConeSecond_factor {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    relativeJoinConeSecond f =
      joinMap (pullback.snd (joinMap f (𝟙 Δ[n])) (joinDiagonal Δ[n])) (𝟙 Δ[0]) ≫
        prismRightConeMap n := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [relativeJoinConeSecond, lift_fst, Category.assoc, prismRightConeMap, lift_fst,
      ← Category.assoc, ← joinMap_comp, Category.id_comp]
    rfl
  · rw [relativeJoinConeSecond, lift_snd, Category.assoc, prismRightConeMap, lift_snd,
      ← Category.assoc, ← joinMap_comp, Category.id_comp]

/-- 概要：恒等射の relative join の右錐の第二成分は単射。
方針：右錐の比較の単射性と、大きい底の引き戻しの第二射影の単射性を使う。
規約：最後の面の包含は単射である。
使われ方：Kerodon Proposition 5.2.4.5、prism の右錐の比較の単射性。 -/
instance relativeJoinConeSecond_id_mono (n : ℕ) :
    Mono (relativeJoinConeSecond (𝟙 (Δ[n] : SSet.{u}))) := by
  rw [← relativeJoinConeMap_snd]
  infer_instance

/-- 概要：prism の右錐の比較は単射。
方針：恒等射の relative join の第二射影の同型で因子化の前の射を打ち消す。
規約：任意の次元 n で成立する。
使われ方：Kerodon Proposition 5.2.4.5、右錐の底の比較を部分複体として扱う段階。 -/
instance prismRightConeMap_mono (n : ℕ) : Mono (prismRightConeMap.{u} n) := by
  let e := joinMap (pullback.snd (joinMap (𝟙 (Δ[n] : SSet.{u})) (𝟙 Δ[n]))
    (joinDiagonal Δ[n])) (𝟙 (Δ[0] : SSet.{u}))
  have : IsIso e := by
    change IsIso ((joinLeftFunctor (Δ[0] : SSet.{u})).map
      (pullback.snd (joinMap (𝟙 (Δ[n] : SSet.{u})) (𝟙 Δ[n])) (joinDiagonal Δ[n])))
    infer_instance
  have he : prismRightConeMap.{u} n = inv e ≫ relativeJoinConeSecond (𝟙 (Δ[n] : SSet.{u})) := by
    apply (cancel_epi e).1
    rw [IsIso.hom_inv_id_assoc]
    exact (relativeJoinConeSecond_factor (𝟙 (Δ[n] : SSet.{u}))).symm
  rw [he]
  infer_instance

end SerrePositivity.InfinityCategories
