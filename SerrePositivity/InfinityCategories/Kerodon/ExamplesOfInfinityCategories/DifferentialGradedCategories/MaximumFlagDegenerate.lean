module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MaximumFlag

/-!
# 最大頂点の旗の反転による退化

概要：既に現れた内部点以下の点を後から加えると最大頂点が繰り返し、最上位評価が零になる。
方針：最大頂点の上界による特徴づけで隣接頂点の等式を示し、非単射な引き戻しを消す。
規約：旗は任意の番号付けで取り、反転する二座標を具体的に指定する。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の比較と最大頂点による逆射の合成の計算。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：後の内部点が先行する点以下なら最大番号の旗の隣接頂点が等しい。
方針：先行する点は既に最大番号以下なので、新しい点を加えても上界が変わらない。
規約：i 番目の点を加える前後を castSucc と succ で指定する。
使われ方：Kerodon 2.5.9（Tag 00SC） の順序に反転のある旗の退化。 -/
lemma maximumFlagOrder_repeat {n : ℕ} (a : Fin (n + 1))
    (S : Finset (Set.Ioo (ULift.up a.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))) {m : ℕ} (e : Fin m ≃ S) (r i : Fin m)
    (hr : r < i) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSourceCoordinate (e i).val ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSourceCoordinate (e r).val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder a S e i.castSucc = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder a S e i.succ := by
  apply le_antisymm
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder a S e).monotone i.castSucc_le_succ
  · have hprev := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder_le_iff a S e i.castSucc
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder a S e i.castSucc)).mp le_rfl
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder_le_iff a S e i.succ _).mpr
    refine ⟨hprev.1, ?_⟩
    intro v hv
    by_cases hvi : (e.symm v).val < i.val
    · exact hprev.2 v hvi
    · have hidx : e.symm v = i := Fin.ext (by
        change (e.symm v).val < i.val + 1 at hv
        omega)
      have hv' : v = e i := by simpa using congrArg e hidx
      subst v
      exact hi.trans (hprev.2 (e r) (by simpa using hr))

open DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y : D}

/-- 概要：最大頂点の旗に沿う標準単体の評価は最大番号の単調写像の引き戻しである。
方針：最大頂点の射の各旗での計算と米田の単体の評価を使う。
規約：Hom の元は標準座標の単体として与える。
使われ方：HA 1.3.1.17 の立方体評価と標準 Hom の成分との比較。 -/
lemma cubeFlagEvaluation_maximum {n : ℕ} (a : Fin (n + 1))
    (S : Finset (Set.Ioo (ULift.up a.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))) {m : ℕ} (e : Fin m ≃ S)
    (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation e
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap (show (ULift.up a.castSucc : ULift.{u} (Fin (n + 2))) <
        ULift.up (Fin.last (n + 1)) from Fin.castSucc_lt_last a) S ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap a ≫ SSet.yonedaEquiv.symm σ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y m (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder a S e) σ) := by
  let φ : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y := SSet.yonedaEquiv.symm σ
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y m
    (φ.app (Opposite.op ⦋m⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap a).app (Opposite.op ⦋m⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap _ S).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e)))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathLastMaximumMap_cubeFlag]
  rfl

/-- 概要：内部座標の反転を持つ最大頂点の旗の評価は零である。
方針：隣接する最大頂点の反復で添字写像の非単射性を示し、その引き戻しの成分を消す。
規約：元の単体に零性や正規化の追加仮定はない。
使われ方：Kerodon 2.5.9（Tag 00SC） の全旗の和を昇順の唯一の旗へ絞る。 -/
lemma cubeFlagEvaluation_maximum_zero_of_inversion {n : ℕ} (a : Fin (n + 1))
    (S : Finset (Set.Ioo (ULift.up a.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))) {m : ℕ} (e : Fin m ≃ S) (r i : Fin m)
    (hr : r < i) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSourceCoordinate (e i).val ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSourceCoordinate (e r).val)
    (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation e
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap (show (ULift.up a.castSucc : ULift.{u} (Fin (n + 2))) <
        ULift.up (Fin.last (n + 1)) from Fin.castSucc_lt_last a) S ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap a ≫ SSet.yonedaEquiv.symm σ) = 0 := by
  rw [cubeFlagEvaluation_maximum]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval_pullback_zero
  intro hinj
  exact (ne_of_lt i.castSucc_lt_succ) (hinj (maximumFlagOrder_repeat a S e r i hr hi))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
