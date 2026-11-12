module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveHornCandidate

/-!
概要：係数に Kan 性を要求せず、指定した最後の係数ホーンの充填から重み付き図式を作る。
方針：既存の最後の面を固定し、同じ係数充填を初区間の図式へ追加する。
規約：実際に指定した充填そのものを使い、追加の存在仮定を主定理へ残さない。
使われ方：quasicategory 値 weighted nerve の inner・cocartesian ホーン充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors

/-- 係数ホーンの実際の充填があれば、最後の面を固定した重み付き図式へ移せる。
方針：充填の最後の面を計算し、元の初区間の図式へ同じ充填を追加する。
規約：係数の Kan 性や quasicategory 性は仮定せず、指定した充填そのものを使う。
使われ方：quasicategory 値 weighted nerve の inner・cocartesian ホーン充填。 -/
lemma exists_weightedNerveHorn_candidate_with_last_of_coefficient_filler
    {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1))
    (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ F.obj (σ.obj (Fin.last (n + 1))))
    (hH : (horn (n + 1) k).ι ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornLastCoefficient F σ k a ha) :
    ∃ ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ σ ⋙ F,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, ψ⟩ =
        SSet.yonedaEquiv (horn.ι k (Fin.last (n + 1)) hk.symm ≫ a) ∧
      (horn (n + 1) k).ι ≫ ψ.app (Fin.last (n + 1)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornLastCoefficient F σ k a ha ∧ ψ.app (Fin.last (n + 1)) = H := by
  let τ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornPrefixDiagram F σ k hk a ha
  let r := horn.ι k (Fin.last (n + 1)) hk.symm
  let α := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)
  have hr : r ≫ (horn (n + 1) k).ι = stdSimplex.map α :=
    (horn.ι_ι k (Fin.last (n + 1)) hk.symm).trans
      (congrArg (fun q ↦ (stdSimplex.map q : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1]))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_eq_lastFace n).symm)
  have hb : stdSimplex.map α ≫ H =
      τ.app (Fin.last n) ≫ (σ ⋙ F).map (homOfLE (Fin.le_last (Fin.last n).castSucc)) := by
    calc
      _ = (r ≫ (horn (n + 1) k).ι) ≫ H := congrArg (fun q ↦ q ≫ H) hr.symm
      _ = r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornLastCoefficient F σ k a ha := by rw [Category.assoc, hH]
      _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_restriction F σ a (horn (n + 1) k).ι ha r α hr τ
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornPrefixDiagram_yoneda F σ k hk a ha)
  let ψ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagramSnocOfLastFace (σ ⋙ F) τ H hb
  have hψ : ψ.app (Fin.last (n + 1)) = H :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagramSnoc_last (σ ⋙ F) τ H
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagram_lastFace_compatible (σ ⋙ F) τ H hb)
  refine ⟨ψ, ?_, ?_, hψ⟩
  · have hp : (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNervePrefixFunctor n ⋙ σ, τ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) =
        SSet.yonedaEquiv (r ≫ a) := by
      apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (n := ⦋n⦌)).symm.injective
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornPrefixDiagram_yoneda F σ k hk a ha).trans
        (SSet.yonedaEquiv.symm_apply_apply _).symm
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexSnoc_lastFace F σ τ H hb).trans hp
  · rw [hψ]
    exact hH

/-- 指定した係数充填から最後の面とホーンを保つ図式を得る。 -/
lemma exists_weightedNerveHorn_candidate_of_coefficient_filler {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1))
    (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ F.obj (σ.obj (Fin.last (n + 1))))
    (hH : (horn (n + 1) k).ι ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornLastCoefficient F σ k a ha) :
    ∃ ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ σ ⋙ F,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, ψ⟩ =
        SSet.yonedaEquiv (horn.ι k (Fin.last (n + 1)) hk.symm ≫ a) ∧
      (horn (n + 1) k).ι ≫ ψ.app (Fin.last (n + 1)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornLastCoefficient F σ k a ha := by
  obtain ⟨ψ, hp, ht, _⟩ :=
    exists_weightedNerveHorn_candidate_with_last_of_coefficient_filler F σ k hk a ha H hH
  exact ⟨ψ, hp, ht⟩

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
