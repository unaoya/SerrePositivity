module
public import SerrePositivity.HomologicalAlgebra.KoszulDualZero
public import SerrePositivity.HomologicalAlgebra.KoszulDualInjectiveAcyclic

/-! # Quotient normalization of all zero-degree dual Koszul power transitions -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite HomologicalComplex
open DerivedCompletion
variable {R : Type u} [CommRing R] {e : ℕ} (z : Fin e → R)

/-- The actual chain H0 quotient normalization respects the original adjacent power maps. -/
lemma koszulChainCanonicalH0Iso_power_transition (n : ℕ) :
    homologyMap (restrictionMap (powerKoszulTransition R z n) embUp) 0 ≫
        (koszulChainCanonicalH0Iso (fun j => z j ^ n)).hom =
      (koszulChainCanonicalH0Iso (fun j => z j ^ (n + 1))).hom ≫
        (localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).map
          (homOfLE (Nat.le_succ n)).op := by
  dsimp only [koszulChainCanonicalH0Iso, Iso.trans_hom]
  erw [← Category.assoc, toChainHomologyIso_hom_naturality (powerKoszulTransition R z n)
    (koszulComplex_isZero_X_of_pos _) (koszulComplex_isZero_X_of_pos _), Category.assoc]
  rw [Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact powerKoszulStageH0Equiv_transition R z n x

/-- Zero dual cohomology identifies each actual power transition with precomposition by
its standard quotient transition, naturally in every coefficient module. -/
lemma koszulDualZeroHomologyNatIso_power_transition (n : ℕ) :
    Functor.whiskerRight (koszulDualPowerTransition z n)
        (homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0) ≫
        (koszulDualZeroHomologyNatIso (fun j => z j ^ (n + 1))).hom =
      (koszulDualZeroHomologyNatIso (fun j => z j ^ n)).hom ≫
        (linearCoyoneda R (ModuleCat.{u} R)).map
          ((localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).map
            (homOfLE (Nat.le_succ n)).op).op := by
  apply NatTrans.ext
  funext J
  let K := toChain (powerKoszulTower R z (n + 1))
  let L := toChain (powerKoszulTower R z n)
  let f : K ⟶ L := restrictionMap (powerKoszulTransition R z n) embUp
  let EK := koszulChainCanonicalH0Iso (fun j => z j ^ (n + 1))
  let EL := koszulChainCanonicalH0Iso (fun j => z j ^ n)
  let q := (localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).map
    (homOfLE (Nat.le_succ n)).op
  let F := (linearYoneda R (ModuleCat.{u} R)).obj J
  have hnorm : homologyMap f 0 ≫ EL.hom = EK.hom ≫ q :=
    koszulChainCanonicalH0Iso_power_transition z n
  have hinv : EK.inv ≫ homologyMap f 0 = q ≫ EL.inv := by
    apply (cancel_mono EL.hom).mp
    simp only [Category.assoc, hnorm, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  change homologyMap ((chainLinearYonedaMap f).app J) 0 ≫
      ((chainLinearYonedaZeroHomologyIso K J).hom ≫ F.map EK.inv.op) =
    ((chainLinearYonedaZeroHomologyIso L J).hom ≫ F.map EL.inv.op) ≫ F.map q.op
  rw [← Category.assoc, chainLinearYonedaZeroHomologyIso_chain_naturality,
    Category.assoc, Category.assoc]
  congr 1
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, hinv]

/-- The direct diagram of Hom from the actual coordinate-power quotients. -/
def powerKoszulQuotientHomDiagram : ℕ ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  opOp ℕ ⋙ (localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).op ⋙
    linearCoyoneda R (ModuleCat.{u} R)

/-- The entire zero dual cohomology diagram agrees with the quotient-Hom diagram. -/
def koszulDualPowerZeroHomologyDiagramNatIso :
    koszulDualPowerHomologyDiagram z 0 ≅ powerKoszulQuotientHomDiagram z := by
  let α : koszulDualPowerHomologyDiagram z 0 ⟶ powerKoszulQuotientHomDiagram z :=
    NatTrans.ofSequence (fun n => (koszulDualZeroHomologyNatIso (fun j => z j ^ n)).hom) (by
      intro n
      simp only [koszulDualPowerHomologyDiagram, koszulDualPowerDiagram,
        Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
        Functor.whiskeringRight_obj_map]
      exact koszulDualZeroHomologyNatIso_power_transition z n)
  exact NatIso.ofComponents (fun n => koszulDualZeroHomologyNatIso (fun j => z j ^ n))
    (fun f => α.naturality f)

/-- The zero homology of the actual dual colimit is the actual quotient-Hom colimit,
naturally in coefficients. No Noetherian or regular-sequence assumption is needed. -/
def koszulDualColimitZeroQuotientHomNatIso :
    koszulDualColimitFunctor z ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0 ≅
      colimit (powerKoszulQuotientHomDiagram z) :=
  asFunctorCochainHomologyIso (koszulDualColimitComplex z) 0 ≪≫
    koszulDualColimitHomologyDiagramIso z 0 ≪≫
    HasColimit.isoOfNatIso (koszulDualPowerZeroHomologyDiagramNatIso z)

end SerrePositivity
