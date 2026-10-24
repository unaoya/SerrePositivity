module
public import SerrePositivity.InfinityCategories.F1.Fibrations.BaseChange
public import SerrePositivity.InfinityCategories.F1.Fibrations.InvertibleCartesian
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.F1B.Localization.Localization

/-! # 全辺が可逆になる底図式上の、元の左 fibration の cartesian 性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 左 fibration を可逆な全辺の図式へ引き戻すと、元の実 lift によって cartesian にもなる。 -/
theorem leftFibrationBaseChange_cartesian_of_inverts {E Q D : SSet.{u}} [Quasicategory Q]
    (p : E ⟶ Q) [LeftFibration p] (k : D ⟶ Q) (hk : InvertsEdges k Set.univ) :
    CartesianFibration (pullback.snd p k) := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  refine ⟨innerFibrations.pullback_snd p k (InnerFibration.mem (q := p)), ?_⟩
  intro v e he
  change stdSimplex.δ (0 : Fin 2) ≫ e =
    yonedaEquiv.symm ((pullback.snd p k).app (Opposite.op ⦋0⦌) v) at he
  let w := (pullback.fst p k).app (Opposite.op ⦋0⦌) v
  have hb : stdSimplex.δ (0 : Fin 2) ≫ (e ≫ k) =
      yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) w) := by
    rw [← Category.assoc, he]
    have hc := congrArg (fun m => m.app (Opposite.op ⦋0⦌) v)
      (pullback.condition (f := p) (g := k))
    apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply, NatTrans.comp_app_apply, w]
      using hc.symm
  have ht : Q.δ 0 (yonedaEquiv (e ≫ k)) = p.app (Opposite.op ⦋0⦌) w := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hb, Equiv.apply_symm_apply]
  let s : Truncated.Edge (X := (truncation 2).obj Q)
      (Q.δ 1 (yonedaEquiv (e ≫ k))) (p.app (Opposite.op ⦋0⦌) w) :=
    ⟨yonedaEquiv (e ≫ k), rfl, ht⟩
  have hs : IsInvertibleEdge s := by
    have hi := hk (a := yonedaEquiv e) (Set.mem_univ _)
    apply (isInvertibleEdge_congr (e := (edgeOfSimplex (yonedaEquiv e)).map
      ((truncation 2).map k)) (f := s) (yonedaEquiv_comp e k).symm).mp
    exact hi
  obtain ⟨G, hG, hGp⟩ := leftFibration_liftInvertibleEdge_target p w s hs
  have hGk : G ≫ p = e ≫ k := hGp.trans (yonedaEquiv.symm_apply_apply _)
  have hGi : IsInvertibleEdge (edgeOfSimplex (yonedaEquiv G)) := by
    apply leftFibration_reflects_invertibleEdge p
    apply (isInvertibleEdge_congr (f := s) (show
      ((edgeOfSimplex (yonedaEquiv G)).map ((truncation 2).map p)).edge = s.edge from
        (yonedaEquiv_comp G p).symm.trans (congrArg SSet.yonedaEquiv hGk))).mpr
    exact hs
  have hGc := isCartesianEdge_of_isInvertibleEdge p (edgeOfSimplex (yonedaEquiv G)) hGi
  refine ⟨pullback.lift G e hGk, ?_, pullback.lift_snd _ _ _, ?_⟩
  · apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst, yonedaEquiv_symm_comp] using hG
    · simpa only [Category.assoc, pullback.lift_snd, yonedaEquiv_symm_comp] using he
  · apply isCartesianEdge_pullback
    rw [← SSet.yonedaEquiv_comp, pullback.lift_fst]
    exact hGc

end SerrePositivity.KST.Fibration
