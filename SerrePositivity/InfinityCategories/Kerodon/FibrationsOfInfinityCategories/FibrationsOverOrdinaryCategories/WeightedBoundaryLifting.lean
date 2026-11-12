module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.WeightedBoundaryReconstruction

/-!
概要：weighted nerve の境界の充填を最後の係数の境界の充填から作る。
方針：最後の面の係数に充填した最後の単体を追加し、境界の復元定理を使う。
規約：底の射列は変更せず、最後の係数の充填だけを入力する。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.4.6（Tag 03BB） の係数図式の比較の持ち上げ性。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
variable {C : Type u} [Category.{u} C]

/-- 概要：最後の係数の境界を充填すると weighted nerve の境界全体を充填できる。
方針：最後の面から初区間の図式を取り出し、係数充填との整合性から最後の成分を追加する。
規約：充填した最後の成分そのものを保持する。
使われ方：Kerodon 5.3.3.1（Tag 025X） の相対境界の構成。 -/
lemma exists_weightedBoundary_filler_of_last (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm σ)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ F.obj (σ.obj (Fin.last (n + 1))))
    (hH : (boundary (n + 1)).ι ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a (boundary (n + 1)).ι ha) :
    ∃ ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ σ ⋙ F,
      (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm
        (⟨σ, ψ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F (n + 1)) = a ∧
      ψ.app (Fin.last (n + 1)) = H := by
  let α := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)
  let r : (Δ[n] : SSet.{u}) ⟶ (boundary (n + 1) : SSet.{u}) :=
    boundary.ι (Fin.last (n + 1))
  have hbase : (SSet.yonedaEquiv (r ≫ a)).1 = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNervePrefixFunctor n ⋙ σ := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNervePrefixFunctor
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_eq_lastFace]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedBoundaryFace_base F σ a ha _
  let τ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexDiagram F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNervePrefixFunctor n ⋙ σ)
    (SSet.yonedaEquiv (r ≫ a)) hbase
  have hτ : SSet.yonedaEquiv.symm
      (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNervePrefixFunctor n ⋙ σ, τ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) = r ≫ a :=
    (congrArg SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexDiagram_eta F _ _ hbase)).trans
        (SSet.yonedaEquiv.symm_apply_apply _)
  have hr : r ≫ (boundary (n + 1)).ι = stdSimplex.map α := by
    dsimp only [α]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_eq_lastFace]
    rfl
  have hb : stdSimplex.map α ≫ H =
      τ.app (Fin.last n) ≫ (σ ⋙ F).map
        (homOfLE (Fin.le_last (Fin.last n).castSucc)) := by
    rw [← hr, Category.assoc, hH]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_restriction F σ a
      (boundary (n + 1)).ι ha r α hr τ hτ
  let ψ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagramSnocOfLastFace (σ ⋙ F) τ H hb
  have hlast : ψ.app (Fin.last (n + 1)) = H :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagramSnoc_last (σ ⋙ F) τ H
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagram_lastFace_compatible (σ ⋙ F) τ H hb)
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ (Fin.last (n + 1))) ⟨σ, ψ⟩ =
      SSet.yonedaEquiv (r ≫ a) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_eq_lastFace]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexSnoc_lastFace F σ τ H hb).trans
      ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (n := ⦋n⦌)).symm.injective
        (hτ.trans (SSet.yonedaEquiv.symm_apply_apply _).symm))
  refine ⟨ψ, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedBoundary_reconstruction F σ a ha ψ hp ?_, hlast⟩
  rw [hlast]
  exact hH

/-- 概要：同じ底上の weighted nerve の係数図式は最後の面と最後の成分で決まる。
方針：最後の面の等式から以前の全ての成分を回収し、最後の成分と合わせる。
規約：底の射列を固定した厳密な一意性。
使われ方：Kerodon 5.3.3.1（Tag 025X） の係数の充填を比較先の指定単体へ写す条件。 -/
lemma weightedDiagram_eq_of_lastFace (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (ψ θ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n))
        ⟨σ, ψ⟩ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, θ⟩)
    (ht : ψ.app (Fin.last (n + 1)) = θ.app (Fin.last (n + 1))) : ψ = θ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagram_ext ?_ ht
  intro i
  have he := NatTrans.congr_app (eq_of_heq (Sigma.mk.inj hp).2) i
  change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) i) ≫ ψ.app i.castSucc =
    stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) i) ≫ θ.app i.castSucc at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_inclusion, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.id_comp] at he
  exact he

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
