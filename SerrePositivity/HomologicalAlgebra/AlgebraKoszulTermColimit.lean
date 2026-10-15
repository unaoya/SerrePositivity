module
public import SerrePositivity.HomologicalAlgebra.AlgebraMappingConeDual
public import SerrePositivity.HomologicalAlgebra.AlgebraKoszulColimit
public import SerrePositivity.HomologicalAlgebra.ScalarWeightedColimit
public import SerrePositivity.HomologicalAlgebra.KoszulWeightedColimit
public import SerrePositivity.HomologicalAlgebra.ColimitLinearFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Actual dual Koszul term diagrams and their colimit splitting -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open DerivedCompletion
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]

/-- The integer-labelled dual term diagram with actual C-linear power transitions. -/
def algebraKoszulPowerDualTermDiagram {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} C) (q : ℤ) : ℕ ⥤ ModuleCat.{u} C :=
  Functor.ofSequence (fun n => ModuleCat.ofHom
    (algebraLinearYonedaPrecomp ((powerKoszulTransition R z n).f q) M))

/-- The old shifted summand has the scalar weight from the newly added coordinate. -/
def algebraKoszulPowerDualWeightedTermDiagram {e : ℕ} (z : Fin (e + 1) → R)
    (M : ModuleCat.{u} C) (q : ℤ) : ℕ ⥤ ModuleCat.{u} C :=
  scalarWeightedSequence (algebraMap R C (z (Fin.last e)))
    (fun n => (algebraKoszulPowerDualTermDiagram (Fin.init z) M q).obj n)
    (fun n => (algebraKoszulPowerDualTermDiagram (Fin.init z) M q).map
      (homOfLE (Nat.le_succ n)))

/-- The entire actual term diagram splits into weighted shifted and unweighted old terms. -/
def algebraKoszulPowerDualTermDiagramSplit {e : ℕ} (z : Fin (e + 1) → R)
    (M : ModuleCat.{u} C) (q : ℤ) :
    algebraKoszulPowerDualTermDiagram z M q ≅
      (pointwiseBinaryBicone
        (algebraKoszulPowerDualWeightedTermDiagram z M (q + 1))
        (algebraKoszulPowerDualTermDiagram (Fin.init z) M q)).pt := by
  let E : ∀ n, (algebraKoszulPowerDualTermDiagram z M q).obj n ≅
      (algebraKoszulPowerDualWeightedTermDiagram z M (q + 1)).obj n ⊞
        (algebraKoszulPowerDualTermDiagram (Fin.init z) M q).obj n := fun n =>
    (algebraKoszulPowerConeHomEquiv z M n q).toModuleIso ≪≫
      (ModuleCat.biprodIsoProd
        ((algebraKoszulPowerDualWeightedTermDiagram z M (q + 1)).obj n)
        ((algebraKoszulPowerDualTermDiagram (Fin.init z) M q).obj n)).symm
  let η : algebraKoszulPowerDualTermDiagram z M q ⟶
      (pointwiseBinaryBicone
        (algebraKoszulPowerDualWeightedTermDiagram z M (q + 1))
        (algebraKoszulPowerDualTermDiagram (Fin.init z) M q)).pt :=
    NatTrans.ofSequence (fun n => (E n).hom) (by
      intro n
      apply biprod.hom_ext
      · simp only [Category.assoc, E, Iso.trans_hom,
          ModuleCat.biprodIsoProd_inv_comp_fst, pointwiseBinaryBicone_pt_map,
          biprod.map_fst, Iso.symm_hom]
        simp only [← Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst]
        simp only [algebraKoszulPowerDualWeightedTermDiagram, scalarWeightedSequence,
          algebraKoszulPowerDualTermDiagram, Functor.ofSequence_map_homOfLE_succ]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        change (algebraKoszulPowerConeHomEquiv z M (n + 1) q
          ((powerKoszulTransition R z n).f q ≫ f)).1 = _
        exact algebraKoszulPowerConeHomEquiv_transition_fst z M n q f
      · simp only [Category.assoc, E, Iso.trans_hom,
          ModuleCat.biprodIsoProd_inv_comp_snd, pointwiseBinaryBicone_pt_map,
          biprod.map_snd, Iso.symm_hom]
        simp only [← Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd]
        simp only [algebraKoszulPowerDualWeightedTermDiagram, scalarWeightedSequence,
          algebraKoszulPowerDualTermDiagram, Functor.ofSequence_map_homOfLE_succ]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        change (algebraKoszulPowerConeHomEquiv z M (n + 1) q
          ((powerKoszulTransition R z n).f q ≫ f)).2 = _
        exact algebraKoszulPowerConeHomEquiv_transition_snd z M n q f)
  exact NatIso.ofComponents E (fun f => η.naturality f)

/-- The actual colimit is the biproduct of the weighted and old colimits. -/
def algebraKoszulPowerDualTermColimitSplit {e : ℕ} (z : Fin (e + 1) → R)
    (M : ModuleCat.{u} C) (q : ℤ) :
    colimit (algebraKoszulPowerDualTermDiagram z M q) ≅
      colimit (algebraKoszulPowerDualWeightedTermDiagram z M (q + 1)) ⊞
        colimit (algebraKoszulPowerDualTermDiagram (Fin.init z) M q) :=
  HasColimit.isoOfNatIso (algebraKoszulPowerDualTermDiagramSplit z M q) ≪≫
    (colim : (ℕ ⥤ ModuleCat.{u} C) ⥤ ModuleCat.{u} C).mapIso
      (biprod.uniqueUpToIso _ _ (pointwiseBinaryBicone.isBilimit _ _)) ≪≫
    (colim : (ℕ ⥤ ModuleCat.{u} C) ⥤ ModuleCat.{u} C).mapBiprod _ _

/-- Restricting the integer Koszul to chain degrees retains actual C-linear dual terms. -/
def algebraKoszulDualTermRestrictionEquiv {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} C) (n i : ℕ) :
    (((algebraKoszulDualFunctor (C := C) (fun j => z j ^ n)).obj M).X i) ≃ₗ[C]
      ((powerKoszulTower R z n).X (-(i : ℤ)) ⟶
        (ModuleCat.restrictScalars (algebraMap R C)).obj M) := by
  let E := (powerKoszulTower R z n).restrictionXIso embUp (i := i)
    (show embUp.f i = -(i : ℤ) by simp [embUp])
  exact
    { algebraLinearYonedaPrecomp E.inv M with
      invFun := fun f => E.hom ≫ f
      left_inv := by intro f; simp [algebraLinearYonedaPrecomp]
      right_inv := by intro f; simp [algebraLinearYonedaPrecomp] }

/-- The actual nonnegative dual power terms agree with the integer-labelled term diagram. -/
def algebraKoszulDualPowerTermDiagramNatIso {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} C) (i : ℕ) :
    algebraKoszulDualPowerDiagram (C := C) z ⋙
        (evaluation (ModuleCat.{u} C) (CochainComplex (ModuleCat.{u} C) ℕ)).obj M ⋙
          eval (ModuleCat.{u} C) (.up ℕ) i ≅
      algebraKoszulPowerDualTermDiagram z M (-(i : ℤ)) := by
  let E := fun n => (algebraKoszulDualTermRestrictionEquiv z M n i).toModuleIso
  let η : algebraKoszulDualPowerDiagram (C := C) z ⋙
      (evaluation (ModuleCat.{u} C) (CochainComplex (ModuleCat.{u} C) ℕ)).obj M ⋙
        eval (ModuleCat.{u} C) (.up ℕ) i ⟶
      algebraKoszulPowerDualTermDiagram z M (-(i : ℤ)) :=
    NatTrans.ofSequence (fun n => (E n).hom) (by
      intro n
      simp only [algebraKoszulDualPowerDiagram, algebraKoszulPowerDualTermDiagram,
        Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      change ((powerKoszulTower R z (n + 1)).restrictionXIso embUp
          (show embUp.f i = -(i : ℤ) by simp [embUp])).inv ≫
          (restrictionMap (powerKoszulTransition R z n) embUp).f i ≫ f =
        (powerKoszulTransition R z n).f (-(i : ℤ)) ≫
          ((powerKoszulTower R z n).restrictionXIso embUp
            (show embUp.f i = -(i : ℤ) by simp [embUp])).inv ≫ f
      rw [restrictionMap_f' (powerKoszulTransition R z n) embUp
        (show embUp.f i = -(i : ℤ) by simp [embUp])]
      simp only [Category.assoc, Iso.inv_hom_id_assoc])
  exact NatIso.ofComponents E (fun f => η.naturality f)

/-- The actual C-module complex colimit terms are the actual colimits of integer dual terms. -/
def algebraKoszulDualColimitTermIso {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} C) (i : ℕ) :
    ((algebraKoszulDualColimitFunctor (C := C) z).obj M).X i ≅
      colimit (algebraKoszulPowerDualTermDiagram z M (-(i : ℤ))) :=
  ((evaluation (ModuleCat.{u} C) (ModuleCat.{u} C)).obj M).mapIso
      (preservesColimitIso (eval (ModuleCat.{u} C ⥤ ModuleCat.{u} C) (.up ℕ) i)
        (algebraKoszulDualFunctorComplexDiagram (C := C) z)) ≪≫
    preservesColimitIso ((evaluation (ModuleCat.{u} C) (ModuleCat.{u} C)).obj M)
      (algebraKoszulDualFunctorComplexDiagram (C := C) z ⋙
        eval (ModuleCat.{u} C ⥤ ModuleCat.{u} C) (.up ℕ) i) ≪≫
    HasColimit.isoOfNatIso (algebraKoszulDualPowerTermDiagramNatIso z M i)

/-- Every positive dual term colimit is acyclic for parameter Koszul operators whose
radical contains the images of the standard coordinates. No regularity is needed. -/
lemma algebraKoszulPowerDualTermColimit_koszulHomology_isZero
    {r : ℕ} (y : Fin r → C) : ∀ {e : ℕ} (z : Fin e → R),
    (∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical) →
    ∀ (M : ModuleCat.{u} C) (q : ℤ), q < 0 → ∀ p : ℤ,
      IsZero (((koszulModuleFunctor y).obj
        (colimit (algebraKoszulPowerDualTermDiagram z M q))).homology p)
  | 0, z, _, M, q, hq, p => by
    have hz : IsZero (algebraKoszulPowerDualTermDiagram z M q) := by
      apply Functor.isZero
      intro n
      have hsource : IsZero ((powerKoszulTower R z n).X q) :=
        isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) q (by omega)
      have : Subsingleton ((algebraKoszulPowerDualTermDiagram z M q).obj n) :=
        ⟨fun f g => hsource.eq_of_src f g⟩
      exact ModuleCat.isZero_of_subsingleton _
    have hc := (colimit.isColimit (algebraKoszulPowerDualTermDiagram z M q)).isZero_pt hz
    exact ((koszulModuleFunctor y) ⋙ homologyFunctor (ModuleCat.{u} C) (.up ℤ) p).map_isZero hc
  | e + 1, z, hz, M, q, hq, p => by
    let F := koszulModuleFunctor y ⋙ homologyFunctor (ModuleCat.{u} C) (.up ℤ) p
    have hweighted : IsZero
        (F.obj (colimit (algebraKoszulPowerDualWeightedTermDiagram z M (q + 1)))) :=
      koszulWeightedColimit_homology_isZero (RingHom.id C) y
        (algebraMap R C (z (Fin.last e))) (hz (Fin.last e)) _ _ p
    have hold := algebraKoszulPowerDualTermColimit_koszulHomology_isZero y
      (Fin.init z) (fun j => hz j.castSucc) M q hq p
    exact ((biprod_isZero_iff _ _).mpr ⟨hweighted, hold⟩).of_iso
      (F.mapIso (algebraKoszulPowerDualTermColimitSplit z M q) ≪≫ F.mapBiprod _ _)

/-- Positive terms of the actual coefficient-algebra colimit complex are
parameter-Koszul acyclic. -/
lemma algebraKoszulDualColimit_positive_term_koszulHomology_isZero
    {e r : ℕ} (z : Fin e → R) (y : Fin r → C)
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical)
    (M : ModuleCat.{u} C) (i : ℕ) (p : ℤ) :
    IsZero (((koszulModuleFunctor y).obj
      (((algebraKoszulDualColimitFunctor (C := C) z).obj M).X (i + 1))).homology p) :=
  (algebraKoszulPowerDualTermColimit_koszulHomology_isZero y z hz M
      (-((i + 1 : ℕ) : ℤ)) (by omega) p).of_iso
    (((koszulModuleFunctor y) ⋙ homologyFunctor (ModuleCat.{u} C) (.up ℤ) p).mapIso
      (algebraKoszulDualColimitTermIso z M (i + 1)))

end SerrePositivity
