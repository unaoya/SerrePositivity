module
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomologyNaturalIso
public import SerrePositivity.DifferentialGraded.Complexes.CoproductHomologySupport
public import SerrePositivity.DifferentialGraded.Derived.Coproducts
public import SerrePositivity.DifferentialGraded.Module.Colimits

/-! # 代表加群からの導来射の余積における有限support -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 主局所化での余積包含に沿う有限support表示。
族が射影的ならこのcofanは主導来圏の実際の余積である。 -/
lemma moduleRepresentableDerivedCoproduct_rep {J : Type u} (x : D)
    (M : J → ModuleCategory A D)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj (∐ M)) :
    ∃ (t : Finset J)
      (g : ∀ j, (moduleToDerived A D).obj
        (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ (moduleToDerived A D).obj (M j)),
      ∑ j ∈ t, g j ≫ (moduleToDerived A D).map (Sigma.ι M j) = f := by
  classical
  let E := moduleEvaluation A D x
  let s : Cofan (fun j => E.obj (M j)) :=
    Cofan.mk (E.obj (∐ M)) (fun j => E.map (Sigma.ι M j))
  have hs : IsColimit s := isColimitCofanMkObjOfIsColimit E M _ (coproductIsCoproduct M)
  obtain ⟨t, c, hc⟩ := complexCofan_zeroHomology_rep A (fun j => E.obj (M j)) s hs
    (moduleRepresentableDerivedHomologyEquiv A D x (∐ M) f)
  let g := fun j => (moduleRepresentableDerivedHomologyEquiv A D x (M j)).symm (c j)
  refine ⟨t, g, ?_⟩
  apply (moduleRepresentableDerivedHomologyEquiv A D x (∐ M)).injective
  calc
    _ = ∑ j ∈ t, moduleRepresentableDerivedHomologyEquiv A D x (∐ M)
        (g j ≫ (moduleToDerived A D).map (Sigma.ι M j)) :=
      map_sum (moduleRepresentableDerivedHomologyLinearEquiv A D x (∐ M)).toLinearMap _ _
    _ = ∑ j ∈ t, homologyMap (s.inj j) 0 (c j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [moduleRepresentableDerivedHomologyEquiv_postcompose]
      change homologyMap (s.inj j) 0
        ((moduleRepresentableDerivedHomologyEquiv A D x (M j))
          ((moduleRepresentableDerivedHomologyEquiv A D x (M j)).symm (c j))) = _
      rw [Equiv.apply_symm_apply]
    _ = _ := hc

end SerrePositivity.DifferentialGraded
