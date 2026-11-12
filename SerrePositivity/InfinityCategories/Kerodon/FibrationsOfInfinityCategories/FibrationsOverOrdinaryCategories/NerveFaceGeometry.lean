module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveLastFace
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
概要：最後の頂点を避ける面の初区間を、全体の最後の面へ因子分解する。
方針：単調写像の初区間への制限を使い、ホーン内の射の等式を包含後に確認する。
規約：ホーンの欠ける面は最後以外。
使われ方：Kerodon §5.3.3（Tag 025W）、再構成した weighted nerve の面の初区間の一致。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：weighted nerve の単体の制限は単調写像の合成を保つ。
方針：単体集合の反変な関手の合成則を各単体で評価する。
規約：α の後に β を合成する。
使われ方：Kerodon §5.3.3（Tag 025W）、ホーン面の交わりを二通りに制限した単体の比較。 -/
lemma weightedNerveSimplexMap_comp {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {l m n : ℕ} (α : ⦋l⦌ ⟶ ⦋m⦌) (β : ⦋m⦌ ⟶ ⦋n⦌) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F α (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F β s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (α ≫ β) s :=
  (ConcreteCategory.congr_hom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F).map_comp β.op α.op) s).symm

/-- 概要：最後の頂点を避ける初区間の像を、一つ短い標準単体へ写す。
方針：初区間で制限した単調写像の標的を全体の最後の面へ含める。
規約：hi は α(i)≤n の条件。
使われ方：Kerodon §5.3.3（Tag 025W）、面の初区間を最後の面と比較するための因子。 -/
def simplexPrefixThroughLast {n : ℕ} (α : ⦋n⦌ ⟶ ⦋n + 1⦌) (i : Fin (n + 1))
    (hi : (α.toOrderHom i).val ≤ n) : ⦋i.val⦌ ⟶ ⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion (α.toOrderHom i).val n hi

/-- 概要：初区間の最後の面への因子分解は元の単調写像と可換。
方針：初区間包含の合成則と制限の因子分解の式を使う。
規約：α は任意の単調写像。
使われ方：Kerodon §5.3.3（Tag 025W）、ホーンの二つの面の交わりの射の等式。 -/
lemma simplexPrefixThroughLast_factor {n : ℕ} (α : ⦋n⦌ ⟶ ⦋n + 1⦌) (i : Fin (n + 1))
    (hi : (α.toOrderHom i).val ≤ n) :
    simplexPrefixThroughLast α i hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt) ≫ α := by
  unfold simplexPrefixThroughLast
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_factor]

/-- 概要：最後の面へ因子分解した射の最後の初区間の制限は元の α の制限。
方針：各頂点の自然数の値を計算する。
規約：標準単体の長さの表示は同じ頂点の値で同定される。
使われ方：Kerodon §5.3.3（Tag 025W）、交わりの単体の最後の成分を元の図式の成分へ戻す式。 -/
lemma simplexPrefixThroughLast_restriction {n : ℕ} (α : ⦋n⦌ ⟶ ⦋n + 1⦌) (i : Fin (n + 1))
    (hi : (α.toOrderHom i).val ≤ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction (simplexPrefixThroughLast α i hi) (Fin.last i.val) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α i := by
  apply SimplexCategory.Hom.ext
  rfl

/-- 概要：最後以外の面の包含は最後の頂点を保つ。
方針：Fin.succAbove の最後の頂点の値の式を使う。
規約：欠ける頂点 j は全体の最後ではない。
使われ方：Kerodon §5.3.3（Tag 025W）、係数輸送が同型になる面の判定。 -/
lemma simplexFace_last_of_ne_last {n : ℕ} (j : Fin (n + 2)) (hj : j ≠ Fin.last (n + 1)) :
    (SimplexCategory.δ j).toOrderHom (Fin.last n) = Fin.last (n + 1) := by
  exact Fin.succAbove_ne_last_last hj

/-- 概要：面の包含で最後の頂点に写る頂点は、その面の最後の頂点。
方針：順序埋め込みの単射性と最後の頂点の最大性を使う。
規約：j の値には制約を課さない。
使われ方：Kerodon §5.3.3（Tag 025W）、面の成分を初区間と最後の成分へ分ける判定。 -/
lemma simplexFace_eq_last_of_image_last {n : ℕ} (j : Fin (n + 2)) (i : Fin (n + 1))
    (h : (SimplexCategory.δ j).toOrderHom i = Fin.last (n + 1)) : i = Fin.last n := by
  apply (Fin.succAboveOrderEmb j).injective
  apply le_antisymm
  · exact (Fin.succAboveOrderEmb j).monotone (Fin.le_last i)
  · change j.succAbove (Fin.last n) ≤ j.succAbove i
    change j.succAbove i = Fin.last (n + 1) at h
    rw [h]
    exact Fin.le_last _

/-- 概要：最後の頂点を避けるホーン面の初区間は最後の面内の射と一致する。
方針：ホーンの包含後に因子分解の式を使い、包含の単射性で戻す。
規約：k≠last により比較先の最後の面もホーンに含まれる。
使われ方：Kerodon §5.3.3（Tag 025W）、元のホーンの面と最後の面の初区間の一致。 -/
lemma horn_face_prefix_through_last {n : ℕ} (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1)) (j : Fin (n + 2)) (hj : j ≠ k)
    (i : Fin (n + 1)) (hi : ((SimplexCategory.δ j).toOrderHom i).val ≤ n) :
    (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)) :
        (Δ[i.val] : SSet.{u}) ⟶ Δ[n]) ≫ horn.ι k j hj =
      stdSimplex.map (simplexPrefixThroughLast (SimplexCategory.δ j) i hi) ≫
        horn.ι k (Fin.last (n + 1)) hk.symm := by
  apply (cancel_mono (horn (n + 1) k).ι).1
  simp only [Category.assoc, horn.ι_ι]
  change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n _) ≫ stdSimplex.map (SimplexCategory.δ j) =
    stdSimplex.map (simplexPrefixThroughLast (SimplexCategory.δ j) i hi) ≫
      stdSimplex.map (SimplexCategory.δ (Fin.last (n + 1)))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_eq_lastFace]
  exact congrArg stdSimplex.map (simplexPrefixThroughLast_factor (SimplexCategory.δ j) i hi).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
