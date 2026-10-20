module
public import SerrePositivity.InfinityCategories.Derived.DGPerfectExtensionInfinity
public import SerrePositivity.InfinityCategories.Derived.DGModuleMoritaInfinity
public import SerrePositivity.InfinityCategories.Derived.DGModuleCompactEquivalence
/-!
概要：graph Morita 同値による Perf の実 ∞ 圏同値。
方針：全射影的加群の同値と perfect の反映から実 H⁰ の本質的全射性を得る。
規約：全 Hom 準同型性も独立に保持。使われ方：β5 の Perf の Morita 不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E : Type v)
variable [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
variable (F : DGFunctor R D E) [(dgDerivedExtension R D E F).IsEquivalence]
/-- graph Morita 同値は射影的模型の同じ H⁰ 関手を同値にする。 -/
lemma dgProjectiveExtension_onHomotopy_isEquivalence :
    (dgProjectiveModuleFunctor R D E (dgModuleExtension R D E F)
      (fun _ h =>
        dgModuleExtension_homotopicallyProjective R D E F h)).onHomotopy.IsEquivalence := by
  let G := dgModuleExtension R D E F
  let hG := fun M (h : dgModuleProjectiveProperty R D M) =>
    dgModuleExtension_homotopicallyProjective R D E F h
  have : (dgModuleClassicalDerivedFunctor R D E G).IsEquivalence := by
    change (dgDerivedExtension R D E F).IsEquivalence
    infer_instance
  have : ((dgProjectiveModuleFunctor R D E G hG).onHomotopy ⋙
      dgProjectiveModuleToDerived R E).IsEquivalence :=
    Functor.isEquivalence_of_iso (dgProjectiveModuleDerivedFunctorIso R D E G hG)
  exact Functor.isEquivalence_of_comp_right _ (dgProjectiveModuleToDerived R E)
/-- graph Morita 同値の perfect 部分圏への制限は実 dg 準同値。 -/
theorem dgPerfectModuleExtension_quasiEquivalence :
    QuasiEquivalence (dgPerfectModuleExtension R D E F) := by
  let G := dgModuleExtension R D E F
  let hG := fun M (h : dgModuleProjectiveProperty R D M) =>
    dgModuleExtension_homotopicallyProjective R D E F h
  let L := dgProjectiveModuleFunctor R D E G hG
  have : L.onHomotopy.IsEquivalence := dgProjectiveExtension_onHomotopy_isEquivalence R D E F
  have hHom := dgProjectiveModuleFunctor_homQuasiIso_of_ho R D E G hG
  refine ⟨?_, ?_⟩
  · intro M N
    change QuasiIso (G.map M.val N.val)
    exact hHom ⟨M.val, M.property.1⟩ ⟨N.val, N.property.1⟩
  · refine ⟨fun Y => ?_⟩
    let y : PerfectDGModule R E := ForgetEnrichment.to (Complex R) Y.as
    let yp : ProjectiveDGModules R E := ⟨y.val, y.property.1⟩
    let Yp := (toHomotopy R (ProjectiveDGModules R E)).obj (ForgetEnrichment.of (Complex R) yp)
    let X := L.onHomotopy.objPreimage Yp
    let x : ProjectiveDGModules R D := ForgetEnrichment.to (Complex R) X.as
    let e := L.onHomotopy.objObjPreimageIso Yp
    let I := dgFullSubcategoryInclusion R (RightModule R E) (dgModuleProjectiveProperty R E)
    have hy : modulePerfect R E ((dgProjectiveModuleToDerived R E).obj Yp) :=
      (modulePerfect R E).prop_of_iso ((moduleToHomotopyDerivedIso R E).app
        (ForgetEnrichment.of (Complex R) y.val)).symm y.property.2
    have hxT : modulePerfect R E ((dgModuleClassicalDerivedFunctor R D E G).obj
        ((dgProjectiveModuleToDerived R D).obj X)) :=
      (modulePerfect R E).prop_of_iso
        (((dgProjectiveModuleDerivedFunctorIso R D E G hG).app X) ≪≫
          (dgProjectiveModuleToDerived R E).mapIso e).symm hy
    have hAdd : (dgModuleClassicalDerivedFunctor R D E G).Additive :=
      dgDerivedExtension_additive R D E F
    have hEq : (dgModuleClassicalDerivedFunctor R D E G).IsEquivalence := by
      change (dgDerivedExtension R D E F).IsEquivalence
      infer_instance
    have : (dgModuleClassicalDerivedFunctor R D E G).asEquivalence.functor.Additive := by
      change (dgModuleClassicalDerivedFunctor R D E G).Additive
      exact hAdd
    have hx : modulePerfect R D ((dgProjectiveModuleToDerived R D).obj X) :=
      (dgModulePerfect_equivalence_iff R D E
        (dgModuleClassicalDerivedFunctor R D E G).asEquivalence _).mp hxT
    have hx' : modulePerfect R D ((moduleToDerived R D).obj
        (ForgetEnrichment.of (Complex R) x.val)) :=
      (modulePerfect R D).prop_of_iso ((moduleToHomotopyDerivedIso R D).app
        (ForgetEnrichment.of (Complex R) x.val)) hx
    let xp : PerfectDGModule R D := ⟨x.val, x.property, hx'⟩
    let Xp := (toHomotopy R (PerfectDGModule R D)).obj (ForgetEnrichment.of (Complex R) xp)
    let J := perfectDGModuleInclusion R E Set.univ
    have ea : J.onHomotopy.obj ((dgPerfectModuleExtension R D E F).onHomotopy.obj Xp) ≅
        J.onHomotopy.obj Y := I.onHomotopy.mapIso e
    exact ⟨Xp, ⟨(Functor.FullyFaithful.ofFullyFaithful J.onHomotopy).preimageIso ea⟩⟩
/-- graph Morita 同値に沿う Perf の実相対 tensor ∞ 関手は同値。 -/
theorem dgPerfectExtensionInfinity_isQCatEquivalence_of_morita :
    IsQCatEquivalence (dgPerfectExtensionInfinity R D E F) :=
  dgNerve_map_isQCatEquivalence_of_quasiEquivalence (dgPerfectModuleExtension R D E F)
    (dgPerfectModuleExtension_quasiEquivalence R D E F)
end SerrePositivity.InfinityCategories
