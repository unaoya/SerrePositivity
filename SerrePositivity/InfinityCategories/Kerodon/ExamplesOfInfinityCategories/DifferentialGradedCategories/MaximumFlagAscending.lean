module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MaximumFlagDegenerate

/-!
# 昇順の Path の旗の最大頂点

概要：内部座標を昇順に加える旗では最大頂点が始点と各座標を順に通る。
方針：最大頂点の上界の特徴づけから各頂点の値と単射性を求める。
規約：昇順の旗では内部点を加えるたびに最大頂点が厳密に増加する。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の逆射との合成に残る唯一の旗。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：内部座標から元の頂点番号への写像は厳密単調である。
方針：ULift と Fin の順序を値の大小に戻す。
規約：端点の上限の変更は順序を変えない。
使われ方：Kerodon 2.5.9（Tag 00SC） の昇順の番号付けの比較。 -/
lemma pathSourceCoordinate_strictMono {n : ℕ} {i : Fin (n + 1)} :
    StrictMono (@_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSourceCoordinate.{u} n i) := fun _ _ h ↦ h

/-- 概要：旗の最初の最大頂点は始点である。
方針：最初の旗には内部点がなく、上界の条件は始点だけになる。
規約：内部座標が空の場合も含む。
使われ方：HA 1.3.1.17 の昇順の旗の最初の頂点。 -/
lemma maximumFlagOrder_zero {n : ℕ} (a : Fin (n + 1))
    (S : Finset (Set.Ioo (ULift.up a.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))) {m : ℕ} (e : Fin m ≃ S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder a S e 0 = a := by
  apply le_antisymm
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder_le_iff a S e 0 a).mpr ⟨le_rfl, by
        intro v hv
        change (e.symm v).val < 0 at hv
        omega⟩
  · exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder_le_iff a S e 0 _).mp le_rfl).1

/-- 概要：昇順の旗で点を加えた直後の最大頂点はその点である。
方針：以前の座標は新しい点以下であり、新しい点自身も既に旗に含まれることを使う。
規約：e の順序は有限内部座標の元の順序を使う。
使われ方：Kerodon 2.5.9（Tag 00SC） の残る旗の全頂点の値。 -/
lemma maximumFlagOrder_succ_of_strictMono {n : ℕ} (a : Fin (n + 1))
    (S : Finset (Set.Ioo (ULift.up a.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))) {m : ℕ} (e : Fin m ≃ S) (he : StrictMono e)
    (j : Fin m) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder a S e j.succ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSourceCoordinate (e j).val := by
  apply le_antisymm
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder_le_iff a S e j.succ _).mpr
    refine ⟨(show a < _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSourceCoordinate (e j).val from (e j).val.property.1).le, ?_⟩
    intro v hv
    have hr : e.symm v ≤ j := by
      change (e.symm v).val < j.val + 1 at hv
      exact (show (e.symm v).val ≤ j.val by omega)
    have hle := he.monotone hr
    have heq : e (e.symm v) = v := e.apply_symm_apply v
    rw [heq] at hle
    exact pathSourceCoordinate_strictMono.monotone hle
  · exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder_le_iff a S e j.succ _).mp le_rfl).2 (e j) (by simp)

/-- 概要：昇順に全内部座標を加える最大番号の旗は厳密単調である。
方針：最初の段階は始点と最初の内部点、その後は隣接する内部点を比較する。
規約：零次元では条件は空である。
使われ方：HA 1.3.1.17 の最上位評価の単射な引き戻し。 -/
lemma maximumFlagOrder_strictMono {n : ℕ} (a : Fin (n + 1))
    (S : Finset (Set.Ioo (ULift.up a.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))) {m : ℕ} (e : Fin m ≃ S) (he : StrictMono e) :
    StrictMono (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.maximumFlagOrder a S e) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro j
  by_cases hj : j.val = 0
  · have hj' : j.castSucc = 0 := Fin.ext hj
    rw [hj', maximumFlagOrder_zero, maximumFlagOrder_succ_of_strictMono a S e he j]
    exact (e j).val.property.1
  · let p : Fin m := ⟨j.val - 1, by omega⟩
    have hp : p.succ = j.castSucc := Fin.ext (by dsimp [p]; omega)
    rw [← hp, maximumFlagOrder_succ_of_strictMono a S e he p,
      maximumFlagOrder_succ_of_strictMono a S e he j]
    apply pathSourceCoordinate_strictMono
    exact he (show p < j by change j.val - 1 < j.val; omega)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
