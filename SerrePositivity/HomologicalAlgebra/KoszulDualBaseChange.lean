module
public import SerrePositivity.HomologicalAlgebra.AlgebraLinearYonedaBaseChange
public import SerrePositivity.HomologicalAlgebra.KoszulBaseChangeNaturality
public import SerrePositivity.HomologicalAlgebra.AlgebraKoszulColimit
public import SerrePositivity.HomologicalAlgebra.LocalCohomologyKoszulComparison

/-! # Coefficient-ring change for the actual dual power-Koszul diagram -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex DerivedCompletion
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {e : ℕ} (z : Fin e → R)

/-- Restrict the standard power-Koszul base-change isomorphism to chain degrees. -/
def baseChangePowerKoszulChainIso (n : ℕ) :
    ((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (.down ℕ)).obj
        (toChain (powerKoszulTower R z n)) ≅
      toChain (powerKoszulTower S ((algebraMap R S) ∘ z) n) :=
  (embUp.restrictionFunctor (ModuleCat.{u} S)).mapIso
    (baseChangePowerKoszulIso (algebraMap R S) z n)

/-- A literal power-Koszul dual over S agrees with the actual S-linear
coefficient dual over R. -/
def koszulDualPowerBaseChangeNatIso (n : ℕ) :
    koszulDualModuleFunctor (fun i => ((algebraMap R S) (z i)) ^ n) ≅
      algebraKoszulDualFunctor (C := S) (fun i => z i ^ n) :=
  chainLinearYonedaMapIso (baseChangePowerKoszulChainIso (S := S) z n) ≪≫
    chainLinearYonedaBaseChangeNatIso (S := S) (toChain (powerKoszulTower R z n))

/-- The coefficient comparison commutes with the actual adjacent dual transitions. -/
lemma koszulDualPowerBaseChangeNatIso_transition (n : ℕ) :
    koszulDualPowerTransition ((algebraMap R S) ∘ z) n ≫
        (koszulDualPowerBaseChangeNatIso (S := S) z (n + 1)).hom =
      (koszulDualPowerBaseChangeNatIso (S := S) z n).hom ≫
        algebraKoszulDualPowerTransition (C := S) z n := by
  let E := baseChangePowerKoszulChainIso (S := S) z
  let f := restrictionMap (powerKoszulTransition R z n) embUp
  let g := restrictionMap (powerKoszulTransition S ((algebraMap R S) ∘ z) n) embUp
  have h : ((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (.down ℕ)).map f ≫
      (E n).hom = (E (n + 1)).hom ≫ g := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact congrArg (fun t => t.f (embUp.f i))
      (baseChangePowerKoszulIso_transition (algebraMap R S) z n)
  change chainLinearYonedaMap g ≫
      (chainLinearYonedaMap (E (n + 1)).hom ≫
        (chainLinearYonedaBaseChangeNatIso (S := S) _).hom) =
    (chainLinearYonedaMap (E n).hom ≫
      (chainLinearYonedaBaseChangeNatIso (S := S) _).hom) ≫ algebraLinearYonedaMap f
  rw [← Category.assoc, ← chainLinearYonedaMap_comp, ← h,
    chainLinearYonedaMap_comp, Category.assoc,
    chainLinearYonedaBaseChangeNatIso_chain_map, ← Category.assoc]

/-- Entire actual dual power diagrams compare over the coefficient algebra,
including every composed transition and every coefficient map. -/
def koszulDualPowerBaseChangeDiagramNatIso :
    koszulDualPowerDiagram ((algebraMap R S) ∘ z) ≅
      algebraKoszulDualPowerDiagram (C := S) z := by
  let α : koszulDualPowerDiagram ((algebraMap R S) ∘ z) ⟶
      algebraKoszulDualPowerDiagram (C := S) z :=
    NatTrans.ofSequence (fun n => (koszulDualPowerBaseChangeNatIso (S := S) z n).hom) (by
      intro n
      simp only [koszulDualPowerDiagram, algebraKoszulDualPowerDiagram,
        CategoryTheory.Functor.ofSequence_map_homOfLE_succ]
      exact koszulDualPowerBaseChangeNatIso_transition (S := S) z n)
  exact NatIso.ofComponents (koszulDualPowerBaseChangeNatIso (S := S) z)
    (fun f => α.naturality f)

/-- Coefficient-ring change compares the actual colimit complexes of coefficient functors. -/
def koszulDualColimitBaseChangeIso :
    koszulDualColimitComplex ((algebraMap R S) ∘ z) ≅
      algebraKoszulDualColimitComplex (C := S) z :=
  HasColimit.isoOfNatIso (Functor.isoWhiskerRight
    (koszulDualPowerBaseChangeDiagramNatIso (S := S) z)
    (functorCochainComplexFunctor (ModuleCat.{u} S) (ModuleCat.{u} S)))

end SerrePositivity
