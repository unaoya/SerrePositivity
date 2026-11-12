module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectExtensionInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleMoritaInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleCompactEquivalence
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E : Type v)
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
variable (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) [(_root_.SerrePositivity.DifferentialGraded.dgDerivedExtension R D E F).IsEquivalence]
/-- graph Morita 同値は射影的模型の同じ H⁰ 関手を同値にする。 -/
lemma dgProjectiveExtension_onHomotopy_isEquivalence :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E (dgModuleExtension R D E F)
      (fun _ h =>
        _root_.SerrePositivity.DifferentialGraded.dgModuleExtension_homotopicallyProjective R D E F h)).onHomotopy.IsEquivalence := by
  let G := _root_.SerrePositivity.DifferentialGraded.dgModuleExtension R D E F
  let hG := fun M (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D M) =>
    _root_.SerrePositivity.DifferentialGraded.dgModuleExtension_homotopicallyProjective R D E F h
  have : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClassicalDerivedFunctor R D E G).IsEquivalence := by
    change (_root_.SerrePositivity.DifferentialGraded.dgDerivedExtension R D E F).IsEquivalence
    infer_instance
  have : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E G hG).onHomotopy ⋙
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleToDerived R E).IsEquivalence :=
    Functor.isEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleDerivedFunctorIso R D E G hG)
  exact Functor.isEquivalence_of_comp_right _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleToDerived R E)
/-- graph Morita 同値の perfect 部分圏への制限は実 dg 準同値。 -/
theorem dgPerfectModuleExtension_quasiEquivalence :
    QuasiEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleExtension R D E F) := by
  let G := _root_.SerrePositivity.DifferentialGraded.dgModuleExtension R D E F
  let hG := fun M (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D M) =>
    _root_.SerrePositivity.DifferentialGraded.dgModuleExtension_homotopicallyProjective R D E F h
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E G hG
  have : L.onHomotopy.IsEquivalence := dgProjectiveExtension_onHomotopy_isEquivalence R D E F
  have hHom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor_homQuasiIso_of_ho R D E G hG
  refine ⟨?_, ?_⟩
  · intro M N
    change QuasiIso (G.map M.val N.val)
    exact hHom ⟨M.val, M.property.1⟩ ⟨N.val, N.property.1⟩
  · refine ⟨fun Y => ?_⟩
    let y : PerfectDGModule R E := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) Y.as
    let yp : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R E := ⟨y.val, y.property.1⟩
    let Yp := (toHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R E)).obj (ForgetEnrichment.of (Complex R) yp)
    let X := L.onHomotopy.objPreimage Yp
    let x : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D := ForgetEnrichment.to (Complex R) X.as
    let e := L.onHomotopy.objObjPreimageIso Yp
    let I := dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R E)
    have hy : modulePerfect R E ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleToDerived R E).obj Yp) :=
      (_root_.SerrePositivity.DifferentialGraded.modulePerfect R E).prop_of_iso ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R E).app
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y.val)).symm y.property.2
    have hxT : modulePerfect R E ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClassicalDerivedFunctor R D E G).obj
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleToDerived R D).obj X)) :=
      (_root_.SerrePositivity.DifferentialGraded.modulePerfect R E).prop_of_iso
        (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleDerivedFunctorIso R D E G hG).app X) ≪≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleToDerived R E).mapIso e).symm hy
    have hAdd : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClassicalDerivedFunctor R D E G).Additive :=
      _root_.SerrePositivity.DifferentialGraded.dgDerivedExtension_additive R D E F
    have hEq : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClassicalDerivedFunctor R D E G).IsEquivalence := by
      change (_root_.SerrePositivity.DifferentialGraded.dgDerivedExtension R D E F).IsEquivalence
      infer_instance
    have : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClassicalDerivedFunctor R D E G).asEquivalence.functor.Additive := by
      change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClassicalDerivedFunctor R D E G).Additive
      exact hAdd
    have hx : modulePerfect R D ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleToDerived R D).obj X) :=
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfect_equivalence_iff R D E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClassicalDerivedFunctor R D E G).asEquivalence _).mp hxT
    have hx' : _root_.SerrePositivity.DifferentialGraded.modulePerfect R D ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x.val)) :=
      (_root_.SerrePositivity.DifferentialGraded.modulePerfect R D).prop_of_iso ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R D).app
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x.val)) hx
    let xp : PerfectDGModule R D := ⟨x.val, x.property, hx'⟩
    let Xp := (_root_.SerrePositivity.DifferentialGraded.toHomotopy R (_root_.SerrePositivity.DifferentialGraded.PerfectDGModule R D)).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) xp)
    let J := _root_.SerrePositivity.DifferentialGraded.perfectDGModuleInclusion R E Set.univ
    have ea : J.onHomotopy.obj ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleExtension R D E F).onHomotopy.obj Xp) ≅
        J.onHomotopy.obj Y := I.onHomotopy.mapIso e
    exact ⟨Xp, ⟨(Functor.FullyFaithful.ofFullyFaithful J.onHomotopy).preimageIso ea⟩⟩
/-- graph Morita 同値に沿う Perf の実相対 tensor ∞ 関手は同値。 -/
theorem dgPerfectExtensionInfinity_isQCatEquivalence_of_morita :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInfinity R D E F) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isQCatEquivalence_of_quasiEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleExtension R D E F)
    (dgPerfectModuleExtension_quasiEquivalence R D E F)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
