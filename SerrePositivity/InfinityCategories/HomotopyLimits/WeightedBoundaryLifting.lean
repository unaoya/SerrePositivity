module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedBoundaryReconstruction

/-!
概要：weighted nerve の境界の充填を最後の係数の境界の充填から作る。
方針：最後の面の係数に充填した最後の単体を追加し、境界の復元定理を使う。
規約：底の射列は変更せず、最後の係数の充填だけを入力する。
使われ方：Kerodon 5.3.3.1、7.5.4.6 の係数図式の比較の持ち上げ性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {C : Type u} [Category.{u} C]

/-- 概要：最後の係数の境界を充填すると weighted nerve の境界全体を充填できる。
方針：最後の面から初区間の図式を取り出し、係数充填との整合性から最後の成分を追加する。
規約：充填した最後の成分そのものを保持する。
使われ方：Kerodon 5.3.3.1 の相対境界の構成。 -/
lemma exists_weightedBoundary_filler_of_last (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (a : (boundary (n + 1) : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm σ)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ F.obj (σ.obj (Fin.last (n + 1))))
    (hH : (boundary (n + 1)).ι ≫ H =
      weightedNerveSimplexCoefficient F σ a (boundary (n + 1)).ι ha) :
    ∃ ψ : simplexPrefixWeight (n + 1) ⟶ σ ⋙ F,
      (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm
        (⟨σ, ψ⟩ : weightedNerveSimplex F (n + 1)) = a ∧
      ψ.app (Fin.last (n + 1)) = H := by
  let α := simplexPrefixInclusion n (n + 1) (Nat.le_succ n)
  let r : (Δ[n] : SSet.{u}) ⟶ (boundary (n + 1) : SSet.{u}) :=
    boundary.ι (Fin.last (n + 1))
  have hbase : (SSet.yonedaEquiv (r ≫ a)).1 = weightedNervePrefixFunctor n ⋙ σ := by
    unfold weightedNervePrefixFunctor
    rw [simplexPrefixInclusion_eq_lastFace]
    exact weightedBoundaryFace_base F σ a ha _
  let τ := weightedNerveSimplexDiagram F (weightedNervePrefixFunctor n ⋙ σ)
    (SSet.yonedaEquiv (r ≫ a)) hbase
  have hτ : SSet.yonedaEquiv.symm
      (⟨weightedNervePrefixFunctor n ⋙ σ, τ⟩ : weightedNerveSimplex F n) = r ≫ a :=
    (congrArg SSet.yonedaEquiv.symm
      (weightedNerveSimplexDiagram_eta F _ _ hbase)).trans
        (SSet.yonedaEquiv.symm_apply_apply _)
  have hr : r ≫ (boundary (n + 1)).ι = stdSimplex.map α := by
    dsimp only [α]
    rw [simplexPrefixInclusion_eq_lastFace]
    rfl
  have hb : stdSimplex.map α ≫ H =
      τ.app (Fin.last n) ≫ (σ ⋙ F).map
        (homOfLE (Fin.le_last (Fin.last n).castSucc)) := by
    rw [← hr, Category.assoc, hH]
    exact weightedNerveSimplexCoefficient_restriction F σ a
      (boundary (n + 1)).ι ha r α hr τ hτ
  let ψ := weightedNerveDiagramSnocOfLastFace (σ ⋙ F) τ H hb
  have hlast : ψ.app (Fin.last (n + 1)) = H :=
    weightedNerveDiagramSnoc_last (σ ⋙ F) τ H
      (weightedNerveDiagram_lastFace_compatible (σ ⋙ F) τ H hb)
  have hp : weightedNerveSimplexMap F (SimplexCategory.δ (Fin.last (n + 1))) ⟨σ, ψ⟩ =
      SSet.yonedaEquiv (r ≫ a) := by
    rw [← simplexPrefixInclusion_eq_lastFace]
    exact (weightedNerveSimplexSnoc_lastFace F σ τ H hb).trans
      ((SSet.yonedaEquiv (X := weightedNerve F) (n := ⦋n⦌)).symm.injective
        (hτ.trans (SSet.yonedaEquiv.symm_apply_apply _).symm))
  refine ⟨ψ, weightedBoundary_reconstruction F σ a ha ψ hp ?_, hlast⟩
  rw [hlast]
  exact hH

/-- 概要：同じ底上の weighted nerve の係数図式は最後の面と最後の成分で決まる。
方針：最後の面の等式から以前の全ての成分を回収し、最後の成分と合わせる。
規約：底の射列を固定した厳密な一意性。
使われ方：Kerodon 5.3.3.1 の係数の充填を比較先の指定単体へ写す条件。 -/
lemma weightedDiagram_eq_of_lastFace (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (ψ θ : simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hp : weightedNerveSimplexMap F (simplexPrefixInclusion n (n + 1) (Nat.le_succ n))
        ⟨σ, ψ⟩ = weightedNerveSimplexMap F
          (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, θ⟩)
    (ht : ψ.app (Fin.last (n + 1)) = θ.app (Fin.last (n + 1))) : ψ = θ := by
  apply weightedNerveDiagram_ext ?_ ht
  intro i
  have he := NatTrans.congr_app (eq_of_heq (Sigma.mk.inj hp).2) i
  change stdSimplex.map (simplexPrefixRestriction
      (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) i) ≫ ψ.app i.castSucc =
    stdSimplex.map (simplexPrefixRestriction
      (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) i) ≫ θ.app i.castSucc at he
  rw [simplexPrefixRestriction_inclusion, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.id_comp] at he
  exact he

end SerrePositivity.InfinityCategories.HomotopyLimits
