module

public import SerrePositivity.InfinityCategories.F1.Weighted.NerveLastFace
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
概要：最後の係数値での左ホーン充填を、weighted nerve の重みの図式の延長へ移す。
方針：Kan 性で最後の単体を充填し、既存の最後の面との整合性から初区間の図式を延長する。
規約：欠ける面は最後以外であり、最後の面は既存の図式の輸送に一致する。
使われ方：Kerodon §5.3.3、Kan 値 weighted nerve の left fibration 性の充填段階。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：最後の係数の左ホーンを充填して、初区間の図式を保った延長を得る。
方針：最後の値の Kan 充填の最後の面を確認し、最後の単体の追加を適用する。
規約：他の面は入力 f で指定し、全ての指定面を最後の成分で厳密に保つ。
使われ方：Kerodon §5.3.3、weighted nerve の左ホーンの最後の係数値での充填。 -/
lemma exists_weightedNerveDiagram_extension_of_lastHorn {n : ℕ}
    (G : Fin (n + 2) ⥤ SSet.{u}) [KanComplex (G.obj (Fin.last (n + 1)))]
    (τ : simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ G)
    (k : Fin (n + 2)) (hk : k ≠ Fin.last (n + 1))
    (f : ∀ (j : Fin (n + 2)) (_hj : j ≠ k), (Δ[n] : SSet.{u}) ⟶ G.obj (Fin.last (n + 1)))
    (hf : horn.IsCompatible f)
    (hlast : f (Fin.last (n + 1)) hk.symm =
      τ.app (Fin.last n) ≫ G.map (homOfLE (Fin.le_last (Fin.last n).castSucc))) :
    ∃ ψ : simplexPrefixWeight (n + 1) ⟶ G,
      (∀ i : Fin (n + 1), ψ.app i.castSucc = τ.app i) ∧
      ∀ j (hj : j ≠ k), stdSimplex.δ j ≫ ψ.app (Fin.last (n + 1)) = f j hj := by
  obtain ⟨H, hH⟩ := hf.exists_lift_of_kanComplex
  have hb : stdSimplex.map (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ≫ H =
      τ.app (Fin.last n) ≫ G.map (homOfLE (Fin.le_last (Fin.last n).castSucc)) := by
    rw [simplexPrefixInclusion_eq_lastFace]
    exact (hH (Fin.last (n + 1)) hk.symm).trans hlast
  refine ⟨weightedNerveDiagramSnocOfLastFace G τ H hb, ?_, ?_⟩
  · intro i
    exact weightedNerveDiagramSnoc_castSucc G τ H
      (weightedNerveDiagram_lastFace_compatible G τ H hb) i
  · intro j hj
    have he : (weightedNerveDiagramSnocOfLastFace G τ H hb).app (Fin.last (n + 1)) = H :=
      weightedNerveDiagramSnoc_last G τ H (weightedNerveDiagram_lastFace_compatible G τ H hb)
    rw [he]
    exact hH j hj

end SerrePositivity.InfinityCategories
