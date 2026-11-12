module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinPrismBoundary
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne

/-!
概要：最後より前の切替位置を持つ prism の最大単体の境界 relative join への因子化。
方針：最大単体の列挙の零時刻の頂点が最後の係数頂点を避けることを確認する。
規約：区間は左因子として書く。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、Z(m) を生成する最大単体の像。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：prism の切替位置 k に対応する最大単体。
方針：Mathlib の列挙の二成分を入れ替えて区間を左因子にする。
規約：次数は m+1、係数の単体は k 番目の退化。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、Proposition 5.2.4.5（Tag 024R） の prism の分解。 -/
noncomputable def relativeJoinPrismShuffle (m : ℕ) (k : Fin (m + 1)) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]) _⦋m + 1⦌ :=
  ⟨(prodStdSimplex₁.nonDegenerateEquiv k).val.2,
    (prodStdSimplex₁.nonDegenerateEquiv k).val.1⟩

/-- 概要：最後より前で切り替わる最大単体は零時刻に最後の係数頂点を持たない。
方針：零時刻の頂点の添字は k 以下であり、退化の順序写像はそこで値を変えない。
規約：k が最後の頂点より小さいことを要求する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、境界へ写る最大単体の判定。 -/
lemma relativeJoinPrismShuffle_no_last_zero (m : ℕ) (k : Fin (m + 1))
    (hk : k < Fin.last m) (i : Fin (m + 2))
    (hi : ((relativeJoinPrismShuffle.{u} m k).1 i).val = 0) :
    (relativeJoinPrismShuffle.{u} m k).2 i ≠ Fin.last m := by
  have ht : stdSimplex.objMk₁.{u} k.succ.castSucc i = 0 := Fin.ext hi
  have hit := (stdSimplex.objMk₁_apply_eq_zero_iff.{u} k.succ.castSucc i).mp ht
  have hik : i ≤ k.castSucc := by
    change i.val ≤ k.val
    change i.val < k.val + 1 at hit
    omega
  change k.predAbove i ≠ Fin.last m
  rw [Fin.predAbove_of_le_castSucc k i hik]
  intro he
  have hv := congrArg Fin.val he
  have hki : k.val < m := hk
  have hii : i.val ≤ k.val := hik
  change i.val = m at hv
  omega

/-- 概要：最後より前で切り替わる prism の最大単体の比較像は境界 relative join に入る。
方針：零時刻に最後の係数頂点を避けることを境界への像の一般判定に適用する。
規約：構造射 f の終域は任意。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、Z(m) の境界側への因子化。 -/
lemma relativeJoinPrismShuffle_mem_boundary {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) (k : Fin (m + 1)) (hk : k < Fin.last m) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f).app (Opposite.op ⦋m + 1⦌) (relativeJoinPrismShuffle.{u} m k) ∈
      Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f)
        (boundary m).ι rfl).app (Opposite.op ⦋m + 1⦌)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_mem_boundary_of_no_last_zero f _ _
    (relativeJoinPrismShuffle_no_last_zero.{u} m k hk)

/-- 概要：最後より前の prism の最大単体の比較を境界 relative join に持ち上げる。
方針：境界への像の判定から得た単体に Yoneda の対応を使う。
規約：持ち上げの選択は非計算的、次の等式で全体への合成を固定する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、最大単体から Z(m) 全体への貼り合わせ。 -/
noncomputable def relativeJoinPrismShuffleBoundaryLift {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) (k : Fin (m + 1)) (hk : k < Fin.last m) :
    (Δ[m + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin ((boundary m).ι ≫ f) (𝟙 Y) :=
  SSet.yonedaEquiv.symm (Classical.choose (relativeJoinPrismShuffle_mem_boundary f k hk))

/-- 概要：境界への最大単体の持ち上げを全体へ戻すと元の prism の比較になる。
方針：選んだ単体の像の等式を Yoneda の対応で射の等式に戻す。
規約：境界 relative join の包含は左因子の自然な射。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、prism の分解の可換性。 -/
lemma relativeJoinPrismShuffleBoundaryLift_comp {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) (k : Fin (m + 1)) (hk : k < Fin.last m) :
    relativeJoinPrismShuffleBoundaryLift f k hk ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl =
      SSet.yonedaEquiv.symm (relativeJoinPrismShuffle.{u} m k) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f := by
  rw [relativeJoinPrismShuffleBoundaryLift, SSet.yonedaEquiv_symm_comp,
    SSet.yonedaEquiv_symm_comp]
  exact congrArg SSet.yonedaEquiv.symm
    (Classical.choose_spec (relativeJoinPrismShuffle_mem_boundary f k hk))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
