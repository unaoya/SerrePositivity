module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ReversalSign

/-!
# 最大頂点の射による立方体の基本鎖の評価

概要：最大頂点の射で全旗の符号付き和を送ると、昇順の唯一の旗に次数符号を掛けた値となる。
方針：昇順でない旗は反復頂点で消し、降順から昇順への反転の符号を計算する。
規約：元の番号付けは降順とし、座標数に関係なく同じ式を使う。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の比較と最大頂点による逆射の合成。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y : D}

/-- 概要：昇順でない内部座標の旗は最大頂点の射による評価で零になる。
方針：厳密単調性の否定から反転する二点を取り、既存の退化評価を使う。
規約：二点の反転の存在を追加の仮定として要求しない。
使われ方：Kerodon 2.5.9（Tag 00SC） の全ての不要な旗の一括消去。 -/
lemma cubeFlagEvaluation_maximum_zero_of_not_strictMono {n : ℕ} (a : Fin (n + 1))
    (S : Finset (Set.Ioo (ULift.up a.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))) {m : ℕ} (e : Fin m ≃ S) (he : ¬ StrictMono e)
    (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation e
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap (show (ULift.up a.castSucc : ULift.{u} (Fin (n + 2))) <
        ULift.up (Fin.last (n + 1)) from Fin.castSucc_lt_last a) S ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap a ≫ SSet.yonedaEquiv.symm σ) = 0 := by
  classical
  change ¬ ∀ r i : Fin m, r < i → e r < e i at he
  push Not at he
  obtain ⟨r, i, hr, hi⟩ := he
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation_maximum_zero_of_inversion a S e r i hr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSourceCoordinate_strictMono.monotone hi) σ

/-- 概要：最大頂点の射での降順立方体評価は昇順旗の引き戻しに次数符号を掛けたもの。
方針：厳密単調な全射の一意性で唯一の反転置換を選び、他の全項を退化で零にする。
規約：零次元も含む。係数は degreeSign m であり、標準座標の符号と同じ。
使われ方：HA 1.3.1.17 の写像空間の比較と逆射の合成が恒等となる計算。 -/
lemma cubeEvaluation_maximum {n : ℕ} (a : Fin (n + 1))
    (S : Finset (Set.Ioo (ULift.up a.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))) {m : ℕ} (e : Fin m ≃ S) (he : StrictAnti e)
    (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap (show (ULift.up a.castSucc : ULift.{u} (Fin (n + 2))) <
        ULift.up (Fin.last (n + 1)) from Fin.castSucc_lt_last a) S ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap a ≫ SSet.yonedaEquiv.symm σ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign m • _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y m
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder a S (Fin.revPerm.trans e)) σ) := by
  have hAsc : StrictMono (Fin.revPerm.trans e) := he.comp Fin.rev_strictAnti
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation
  calc
    _ = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m)) : ℤ) •
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation (Fin.revPerm.trans e) _ := by
      apply Finset.sum_eq_single Fin.revPerm
      · intro τ _ hτ
        have hτ' : ¬ StrictMono (τ.trans e) := by
          intro hτmono
          have heq : τ.trans e = Fin.revPerm.trans e := by
            apply Equiv.ext
            intro j
            exact congrFun (hτmono.eq_of_range_eq hAsc
              ((Set.range_eq_univ.mpr (τ.trans e).surjective).trans
                (Set.range_eq_univ.mpr (Fin.revPerm.trans e).surjective).symm)) j
          apply hτ
          apply Equiv.ext
          intro j
          apply e.injective
          exact congrArg (fun q : Fin m ≃ S ↦ q j) heq
        rw [cubeFlagEvaluation_maximum_zero_of_not_strictMono a S (τ.trans e) hτ' σ,
          smul_zero]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.revPerm_sign, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation_maximum]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
