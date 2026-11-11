module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveLastExtension

/-!
概要：weighted nerve の最後の面を保つ単体の延長。
方針：初区間の包含での重みの制限を計算し、最後の単体を加える構成と接続する。
規約：単体の最後の面は最後の頂点を除く面。
使われ方：Kerodon §5.3.3（Tag 025W）、左ホーンの既存の最後の面を保つ充填。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：標準単体の初区間の包含は最後の面の包含。
方針：最後の頂点を除く Fin.succAbove が castSucc であることを使う。
規約：Δ[n] から Δ[n+1] への射。
使われ方：Kerodon §5.3.3（Tag 025W）、初区間の図式と最後の面の同定。 -/
lemma simplexPrefixInclusion_eq_lastFace (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n) = SimplexCategory.δ (Fin.last (n + 1)) := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  change i.castSucc = (Fin.last (n + 1)).succAbove i
  rw [Fin.succAbove_last]

/-- 概要：初区間の包含をさらに初区間へ制限すると恒等射となる。
方針：有限順序集合の各頂点の値が変わらないことを計算する。
規約：m≤n の包含と m の任意の頂点 i を使う。
使われ方：Kerodon §5.3.3（Tag 025W）、最後の面上の weighted nerve の重みの制限。 -/
lemma simplexPrefixRestriction_inclusion {m n : ℕ} (h : m ≤ n) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion m n h) i = 𝟙 ⦋i.val⦌ := by
  apply SimplexCategory.Hom.ext
  rfl

/-- 概要：最後の単体を加えた図式を最後の面へ制限すると元の初区間の図式になる。
方針：初区間での重みの制限は恒等で、追加した図式の以前の成分は変わらない。
規約：全初区間の整合条件による追加の一般形を扱う。
使われ方：Kerodon §5.3.3（Tag 025W）、最後の面を固定する weighted nerve の単体の延長。 -/
lemma weightedNerveDiagramSnoc_restrict {n : ℕ} (G : Fin (n + 2) ⥤ SSet.{u})
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNervePrefixFunctor n ⋙ G)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ G.obj (Fin.last (n + 1)))
    (hH : ∀ i : Fin (n + 1),
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val (n + 1) (by omega)) ≫ H =
        τ.app i ≫ G.map (homOfLE (Fin.le_last i.castSucc))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeightRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ≫
        CategoryTheory.Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNervePrefixFunctor n)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagramSnoc G τ H hH) = τ := by
  apply NatTrans.ext
  funext i
  change stdSimplex.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) i) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagramSnoc G τ H hH).app i.castSucc = τ.app i
  rw [simplexPrefixRestriction_inclusion, CategoryTheory.Functor.map_id,
    Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagramSnoc_castSucc]

/-- 概要：底の射列と最後の面の図式を、最後の係数値の単体により延長する。
方針：初区間の図式と最後の面で整合する単体を、自然変換の追加で束ねる。
規約：射列 σ 自体は変更しない。
使われ方：Kerodon §5.3.3（Tag 025W）、Kan 充填から weighted nerve のホーン充填を作る構成。 -/
def weightedNerveSimplexSnoc {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C (n + 1))
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNervePrefixFunctor n ⋙ σ ⋙ F)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ F.obj (σ.obj (Fin.last (n + 1))))
    (h : stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ≫ H =
      τ.app (Fin.last n) ≫ F.map (σ.map (homOfLE (Fin.le_last (Fin.last n).castSucc)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F (n + 1) :=
  ⟨σ, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagramSnocOfLastFace (σ ⋙ F) τ H h⟩

/-- 概要：最後の面で整合する単体から作った weighted nerve の単体は指定した面を保つ。
方針：最後の面への制限の式を、追加した図式へ成分ごとに適用する。
規約：底の射列も初区間へ制限される。
使われ方：Kerodon §5.3.3（Tag 025W）、左ホーン充填の既存の最後の面の検査。 -/
lemma weightedNerveSimplexSnoc_lastFace {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C (n + 1))
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNervePrefixFunctor n ⋙ σ ⋙ F)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ F.obj (σ.obj (Fin.last (n + 1))))
    (h : stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ≫ H =
      τ.app (Fin.last n) ≫ F.map (σ.map (homOfLE (Fin.le_last (Fin.last n).castSucc)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n))
        (weightedNerveSimplexSnoc F σ τ H h) = ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNervePrefixFunctor n ⋙ σ, τ⟩ := by
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  exact weightedNerveDiagramSnoc_restrict (σ ⋙ F) τ H
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagram_lastFace_compatible (σ ⋙ F) τ H h)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
