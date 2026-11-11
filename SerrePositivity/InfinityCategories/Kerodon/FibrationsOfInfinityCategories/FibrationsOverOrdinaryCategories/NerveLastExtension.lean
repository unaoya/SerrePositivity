module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Nerve

/-!
概要：weighted nerve の初区間の図式に最後の標準単体を追加する構成。
方針：最後の頂点とそれ以前の頂点に場合分けし、初区間での整合式から自然変換を作る。
規約：係数は有限順序集合上の任意の単体集合値関手。
使われ方：Kerodon §5.3.3（Tag 025W）、weighted nerve の左ホーンを最後の係数値で充填する手順。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：最後の頂点を除いた初区間の順序関手。
方針：標準単体の初区間の包含を有限順序集合の関手に写す。
規約：各頂点 i の値を変えず、i.castSucc に写す。
使われ方：Kerodon §5.3.3（Tag 025W）、最後の頂点を加える前の係数図式の制限。 -/
def weightedNervePrefixFunctor (n : ℕ) : Fin (n + 1) ⥤ Fin (n + 2) :=
  (SimplexCategory.toCat.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n))).toFunctor

/-- 概要：初区間の図式と最後の単体から weighted nerve の重みの図式を作る。
方針：Fin.lastCases で成分を定め、最後へ向かう射の整合条件を自然性に使う。
規約：最後へ向かう全ての初区間での整合条件を明示する。
使われ方：Kerodon §5.3.3（Tag 025W）、左ホーン充填で得た最後の単体の組み込み。 -/
def weightedNerveDiagramSnoc {n : ℕ} (G : Fin (n + 2) ⥤ SSet.{u})
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ G)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ G.obj (Fin.last (n + 1)))
    (hH : ∀ i : Fin (n + 1),
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val (n + 1) (by omega)) ≫ H =
        τ.app i ≫ G.map (homOfLE (Fin.le_last i.castSucc))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ G where
  app i := Fin.lastCases H (fun j ↦ τ.app j) i
  naturality i j f := by
    revert j f
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · intro j f
      have hj : j = Fin.last (n + 1) := le_antisymm (Fin.le_last j) (leOfHom f)
      subst j
      have hf : f = 𝟙 (Fin.last (n + 1)) := Subsingleton.elim _ _
      subst f
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
        Category.id_comp, Category.comp_id]
    · intro j f
      revert f
      refine Fin.lastCases ?_ (fun j ↦ ?_) j
      · intro f
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
        change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val (n + 1) _) ≫ H =
          τ.app i ≫ G.map f
        exact hH i
      · intro f
        simp only [Fin.lastCases_castSucc]
        change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val j.val _) ≫ τ.app j =
          τ.app i ≫ G.map f
        exact τ.naturality (homOfLE (show i ≤ j from leOfHom f))

/-- 概要：最後の単体を加えた図式は以前の頂点で元の成分に一致する。
方針：Fin.lastCases の初区間の分岐を計算する。
規約：i は追加前の有限順序集合の頂点。
使われ方：Kerodon §5.3.3（Tag 025W）、左ホーンの既存の面を保つことの確認。 -/
lemma weightedNerveDiagramSnoc_castSucc {n : ℕ} (G : Fin (n + 2) ⥤ SSet.{u})
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ G)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ G.obj (Fin.last (n + 1)))
    (hH : ∀ i : Fin (n + 1),
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val (n + 1) (by omega)) ≫ H =
        τ.app i ≫ G.map (homOfLE (Fin.le_last i.castSucc))) (i : Fin (n + 1)) :
    (weightedNerveDiagramSnoc G τ H hH).app i.castSucc = τ.app i := by
  simp only [weightedNerveDiagramSnoc, Fin.lastCases_castSucc]

/-- 概要：最後の単体を加えた図式の最後の成分は指定した単体。
方針：Fin.lastCases の最後の分岐を計算する。
規約：追加後の最後の頂点を評価する。
使われ方：Kerodon §5.3.3（Tag 025W）、Kan 充填から得た単体の保持。 -/
lemma weightedNerveDiagramSnoc_last {n : ℕ} (G : Fin (n + 2) ⥤ SSet.{u})
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ G)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ G.obj (Fin.last (n + 1)))
    (hH : ∀ i : Fin (n + 1),
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val (n + 1) (by omega)) ≫ H =
        τ.app i ≫ G.map (homOfLE (Fin.le_last i.castSucc))) :
    (weightedNerveDiagramSnoc G τ H hH).app (Fin.last (n + 1)) = H := by
  simp only [weightedNerveDiagramSnoc, Fin.lastCases_last]

/-- 概要：最後の面で整合する単体は初区間の全てで整合する。
方針：既存の図式の最後の成分への自然性と、初区間包含の合成則を使う。
規約：最後の面は Δ[n] の初区間の包含。
使われ方：Kerodon §5.3.3（Tag 025W）、左ホーン充填を最後の係数値で行うための貼り合わせ。 -/
lemma weightedNerveDiagram_lastFace_compatible {n : ℕ} (G : Fin (n + 2) ⥤ SSet.{u})
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ G)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ G.obj (Fin.last (n + 1)))
    (h : stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ≫ H =
      τ.app (Fin.last n) ≫ G.map (homOfLE (Fin.le_last (Fin.last n).castSucc)))
    (i : Fin (n + 1)) :
    stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val (n + 1) (by omega)) ≫ H =
      τ.app i ≫ G.map (homOfLE (Fin.le_last i.castSucc)) := by
  have ht := τ.naturality (homOfLE (Fin.le_last i))
  change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n _) ≫ τ.app (Fin.last n) =
    τ.app i ≫ G.map (homOfLE (show i.castSucc ≤ (Fin.last n).castSucc from Fin.le_last i)) at ht
  calc
    _ = (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Fin.le_last i)) ≫
        stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n))) ≫ H := by
      rw [← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_comp]
    _ = stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n _) ≫
        (τ.app (Fin.last n) ≫ G.map (homOfLE (Fin.le_last (Fin.last n).castSucc))) := by
      rw [Category.assoc, h]
    _ = (τ.app i ≫ G.map (homOfLE
        (show i.castSucc ≤ (Fin.last n).castSucc from Fin.le_last i))) ≫
        G.map (homOfLE (Fin.le_last (Fin.last n).castSucc)) := by
      rw [← Category.assoc, ht]
    _ = _ := by
      rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
      rfl

/-- 概要：最後の面で整合する単体を初区間の図式へ追加する。
方針：自然性で全初区間の整合性を回収して一般の最後の単体の追加を使う。
規約：入力で要求する等式は最後の面の一つだけ。
使われ方：Kerodon §5.3.3（Tag 025W）、最後の係数値の Kan 充填を weighted nerve の単体にする。 -/
def weightedNerveDiagramSnocOfLastFace {n : ℕ} (G : Fin (n + 2) ⥤ SSet.{u})
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ G)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ G.obj (Fin.last (n + 1)))
    (h : stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ≫ H =
      τ.app (Fin.last n) ≫ G.map (homOfLE (Fin.le_last (Fin.last n).castSucc))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ G :=
  weightedNerveDiagramSnoc G τ H (weightedNerveDiagram_lastFace_compatible G τ H h)

/-- 概要：weighted nerve の重みの図式は初区間の成分と最後の成分で決まる。
方針：有限順序集合の各頂点を最後とそれ以前に場合分けする。
規約：二つの図式は同じ係数関手 G に値を取る。
使われ方：Kerodon §5.3.3（Tag 025W）、充填した weighted nerve の各面の一致の判定。 -/
lemma weightedNerveDiagram_ext {n : ℕ} {G : Fin (n + 2) ⥤ SSet.{u}}
    {τ ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ G}
    (hpre : ∀ i : Fin (n + 1), τ.app i.castSucc = ψ.app i.castSucc)
    (hlast : τ.app (Fin.last (n + 1)) = ψ.app (Fin.last (n + 1))) : τ = ψ := by
  apply NatTrans.ext
  funext i
  exact Fin.lastCases hlast hpre i

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
