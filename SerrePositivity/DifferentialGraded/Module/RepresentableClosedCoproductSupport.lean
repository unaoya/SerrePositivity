module
public import SerrePositivity.DifferentialGraded.Module.RepresentableClosedCycles
public import SerrePositivity.DifferentialGraded.Complexes.CoproductSupport
public import SerrePositivity.DifferentialGraded.Module.Colimits
/-!
概要：代表加群から任意直和への実閉射を、有限個の閉射の和として表示する。
方針：実 Yoneda の零 cycle に余積の有限 support 表示を適用し、閉射へ戻す。
規約：ホモトピー同値ではなく、元の閉射そのものの等式を得る。
使われ方：c′ の自由入力の閉射を有限係数族へ分解する第一段階。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma moduleRepresentableClosedCoproduct_rep {J : Type u} (x : D)
    (M : J → ModuleCategory R D)
    (f : ForgetEnrichment.of (Complex R) (representable R x) ⟶ ∐ M) :
    ∃ (t : Finset J)
      (g : ∀ j, ForgetEnrichment.of (Complex R) (representable R x) ⟶ M j),
      ∑ j ∈ t, g j ≫ Sigma.ι M j = f := by
  classical
  let E := moduleEvaluation R D x
  let s : Cofan (fun j => E.obj (M j)) :=
    Cofan.mk (E.obj (∐ M)) (fun j => E.map (Sigma.ι M j))
  have hs : IsColimit s := isColimitCofanMkObjOfIsColimit E M _ (coproductIsCoproduct M)
  obtain ⟨t, z, hz⟩ := complexCofan_cycle_rep R (fun j => E.obj (M j)) s hs 0
    (representableClosedCycleEquiv R D x (∐ M) f)
  let g := fun j => (representableClosedCycleEquiv R D x (M j)).symm (z j)
  refine ⟨t, g, ?_⟩
  apply (representableClosedCycleEquiv R D x (∐ M)).injective
  apply Subtype.ext
  calc
    _ = ∑ j ∈ t, (representableClosedCycleEquiv R D x (∐ M)
        (g j ≫ Sigma.ι M j)).val := by
      have h := map_sum (representableClosedCycleLinearEquiv R D x (∐ M)).toLinearMap
        (fun j => g j ≫ Sigma.ι M j) t
      change representableClosedCycleEquiv R D x (∐ M) (∑ j ∈ t, g j ≫ Sigma.ι M j) =
        ∑ j ∈ t, representableClosedCycleEquiv R D x (∐ M) (g j ≫ Sigma.ι M j) at h
      simpa only [Submodule.coe_sum] using congrArg Subtype.val h
    _ = ∑ j ∈ t, (s.inj j).f 0 (z j).val := by
      apply Finset.sum_congr rfl
      intro j _
      rw [representableClosedCycleEquiv_postcompose]
      change (s.inj j).f 0
        ((representableClosedCycleEquiv R D x (M j))
          ((representableClosedCycleEquiv R D x (M j)).symm (z j))).val = _
      rw [Equiv.apply_symm_apply]
    _ = _ := hz

end SerrePositivity.DifferentialGraded
