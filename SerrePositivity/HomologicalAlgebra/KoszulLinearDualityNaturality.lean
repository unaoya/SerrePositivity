module
public import SerrePositivity.HomologicalAlgebra.CochainLinearDualConeNaturality
public import SerrePositivity.HomologicalAlgebra.KoszulLinearDuality
public import SerrePositivity.HomologicalAlgebra.ScalarConeShiftNaturality

/-! # Coefficient naturality for the Koszul self-duality construction -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex.homotopyCofiber
variable {R : Type u} [CommRing R]

/-- Replacing the dual scalar map by the actual scalar map preserves its coefficient cone maps. -/
lemma scalarConeLinearDual_eqToHom (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    cochainLinearDualConeCoefficientMap (a • 𝟙 K) f ≫
        eqToHom (show CochainComplex.mappingCone ((cochainLinearDualMap (a • 𝟙 K)).app N) =
          (scalarConeFunctor a).obj ((cochainLinearDualFunctor K).obj N) by
          rw [cochainLinearDualMap_smul_id]; rfl) =
      eqToHom (show CochainComplex.mappingCone ((cochainLinearDualMap (a • 𝟙 K)).app M) =
          (scalarConeFunctor a).obj ((cochainLinearDualFunctor K).obj M) by
          rw [cochainLinearDualMap_smul_id]; rfl) ≫
        (scalarConeFunctor a).map ((cochainLinearDualFunctor K).map f) := by
  exact mappingConeArrowMap_eqToHom _ _ _ _
    (cochainLinearDualMap_smul_id a K M) (cochainLinearDualMap_smul_id a K N)
    (cochainLinearDualConeCoefficientArrow (a • 𝟙 K) f)
    (Arrow.homMk ((cochainLinearDualFunctor K).map f) ((cochainLinearDualFunctor K).map f)
      (by simp)) rfl rfl

/-- The scalar cone dual comparison is natural for all coefficient maps. -/
lemma scalarConeLinearDualIso_naturality (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (cochainLinearDualFunctor ((scalarConeFunctor a).obj K)).map f ≫
        (scalarConeLinearDualIso a K N).hom =
      (scalarConeLinearDualIso a K M).hom ≫
        ((scalarConeFunctor a).map ((cochainLinearDualFunctor K).map f))⟦(-1 : ℤ)⟧' := by
  have h := congrArg ((shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (-1 : ℤ)).map)
    (scalarConeLinearDual_eqToHom a K f)
  simp only [Functor.map_comp] at h
  dsimp only [scalarConeLinearDualIso, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
  rw [← Category.assoc]
  erw [cochainLinearDualConeIso_naturality (a • 𝟙 K) f]
  simpa only [Category.assoc] using congrArg
    (fun g => (cochainLinearDualConeIso (a • 𝟙 K) M).hom ≫ g) h

/-- Empty Koszul duality, evaluation at one, is natural in the coefficient module. -/
lemma koszulLinearDualEmptyIso_naturality (z : Fin 0 → R)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (cochainLinearDualFunctor (koszulComplex z)).map f ≫ (koszulLinearDualEmptyIso z N).hom =
      (koszulLinearDualEmptyIso z M).hom ≫ (koszulModuleFunctor z).map f := by
  apply HomologicalComplex.to_single_hom_ext
  apply ModuleCat.hom_ext
  ext g
  rfl

/-- Scalar cone duality as a natural isomorphism of coefficient functors. -/
def scalarConeLinearDualNatIso (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainLinearDualFunctor ((scalarConeFunctor a).obj K) ≅
      cochainLinearDualFunctor K ⋙ scalarConeFunctor a ⋙ shiftFunctor _ (-1 : ℤ) :=
  NatIso.ofComponents (scalarConeLinearDualIso a K)
    (fun f => scalarConeLinearDualIso_naturality a K f)

/-- Empty Koszul duality as a natural isomorphism. -/
def koszulLinearDualEmptyNatIso (z : Fin 0 → R) :
    cochainLinearDualFunctor (koszulComplex z) ≅ koszulModuleFunctor z :=
  NatIso.ofComponents (koszulLinearDualEmptyIso z)
    (fun f => koszulLinearDualEmptyIso_naturality z f)

/-- The cone-shift comparison is a natural isomorphism of complex functors. -/
def scalarConeShiftNatIso (a : R) (m : ℤ) :
    scalarConeFunctor a ⋙ shiftFunctor _ m ≅ shiftFunctor _ m ⋙ scalarConeFunctor a :=
  NatIso.ofComponents (fun P => scalarConeShiftIso a P m)
    (fun f => scalarConeShiftIso_naturality a f m)

/-- Koszul self-duality is natural for every coefficient module and every coefficient map. -/
def koszulLinearDualNatIso : ∀ {e : ℕ} (z : Fin e → R),
    cochainLinearDualFunctor (koszulComplex z) ≅ koszulModuleFunctor z ⋙ shiftFunctor _ (-(e : ℤ))
  | 0, z => koszulLinearDualEmptyNatIso z ≪≫
      Functor.isoWhiskerLeft (koszulModuleFunctor z)
        (shiftFunctorZero (CochainComplex (ModuleCat.{u} R) ℤ) ℤ).symm
  | n + 1, z =>
      let a := z (Fin.last n)
      scalarConeLinearDualNatIso a (koszulComplex (Fin.init z)) ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerRight (koszulLinearDualNatIso (Fin.init z)) (scalarConeFunctor a))
          (shiftFunctor _ (-1 : ℤ)) ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft (koszulModuleFunctor (Fin.init z))
            (scalarConeShiftNatIso a (-(n : ℤ))).symm) (shiftFunctor _ (-1 : ℤ)) ≪≫
        Functor.isoWhiskerLeft (koszulModuleFunctor z)
          (shiftFunctorAdd' (CochainComplex (ModuleCat.{u} R) ℤ)
            (-(n : ℤ)) (-1) (-((n + 1 : ℕ) : ℤ)) (by omega)).symm

/-- The natural comparison uses exactly the previously constructed self-duality isomorphisms. -/
lemma koszulLinearDualNatIso_app {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R) :
    (koszulLinearDualNatIso z).app M = koszulLinearDualIso z M := by
  induction e with
  | zero => rfl
  | succ n ih =>
    change scalarConeLinearDualIso (z (Fin.last n)) (koszulComplex (Fin.init z)) M ≪≫
        (shiftFunctor _ (-1 : ℤ)).mapIso
          ((scalarConeFunctor (z (Fin.last n))).mapIso
              ((koszulLinearDualNatIso (Fin.init z)).app M) ≪≫
            (scalarConeShiftIso (z (Fin.last n))
              ((koszulModuleFunctor (Fin.init z)).obj M) (-(n : ℤ))).symm) ≪≫
        ((shiftFunctorAdd' (CochainComplex (ModuleCat.{u} R) ℤ)
          (-(n : ℤ)) (-1) (-((n + 1 : ℕ) : ℤ)) (by omega)).app
            ((scalarConeFunctor (z (Fin.last n))).obj
              ((koszulModuleFunctor (Fin.init z)).obj M))).symm = _
    rw [ih]
    rfl

/-- Naturality for the actual self-duality isomorphisms, not just isomorphic replacement objects. -/
lemma koszulLinearDualIso_naturality {e : ℕ} (z : Fin e → R)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (cochainLinearDualFunctor (koszulComplex z)).map f ≫ (koszulLinearDualIso z N).hom =
      (koszulLinearDualIso z M).hom ≫ ((koszulModuleFunctor z).map f)⟦(-(e : ℤ))⟧' := by
  have h := (koszulLinearDualNatIso z).hom.naturality f
  change (cochainLinearDualFunctor (koszulComplex z)).map f ≫
      ((koszulLinearDualNatIso z).app N).hom =
    ((koszulLinearDualNatIso z).app M).hom ≫ ((koszulModuleFunctor z).map f)⟦(-(e : ℤ))⟧' at h
  simpa only [koszulLinearDualNatIso_app] using h

/-- The degree i to degree i-e cohomology comparison is a natural isomorphism. -/
def koszulLinearDualHomologyNatIso {e : ℕ} (z : Fin e → R) (i : ℤ) :
    cochainLinearDualFunctor (koszulComplex z) ⋙ homologyFunctor (ModuleCat R) (.up ℤ) i ≅
      koszulModuleFunctor z ⋙ homologyFunctor (ModuleCat R) (.up ℤ) (i - (e : ℤ)) :=
  Functor.isoWhiskerRight (koszulLinearDualNatIso z) (homologyFunctor (ModuleCat R) (.up ℤ) i) ≪≫
    Functor.isoWhiskerLeft (koszulModuleFunctor z)
      (CochainComplex.ShiftSequence.shiftIso (ModuleCat R) (-(e : ℤ)) i (i - (e : ℤ)) (by omega))

/-- The natural homology comparison also has the previously specified components. -/
lemma koszulLinearDualHomologyNatIso_app {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} R) (i : ℤ) :
    (koszulLinearDualHomologyNatIso z i).app M = koszulLinearDualHomologyIso z M i := by
  change (homologyFunctor (ModuleCat R) (.up ℤ) i).mapIso
      ((koszulLinearDualNatIso z).app M) ≪≫
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat R) (-(e : ℤ)) i
      (i - (e : ℤ)) (by omega)).app ((koszulModuleFunctor z).obj M) = _
  rw [koszulLinearDualNatIso_app]
  rfl

/-- All coefficient maps commute with the actual degree-changing homology isomorphism. -/
lemma koszulLinearDualHomologyIso_naturality {e : ℕ} (z : Fin e → R)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (i : ℤ) :
    homologyMap ((cochainLinearDualFunctor (koszulComplex z)).map f) i ≫
        (koszulLinearDualHomologyIso z N i).hom =
      (koszulLinearDualHomologyIso z M i).hom ≫
        homologyMap ((koszulModuleFunctor z).map f) (i - (e : ℤ)) := by
  have h := (koszulLinearDualHomologyNatIso z i).hom.naturality f
  change homologyMap ((cochainLinearDualFunctor (koszulComplex z)).map f) i ≫
      ((koszulLinearDualHomologyNatIso z i).app N).hom =
    ((koszulLinearDualHomologyNatIso z i).app M).hom ≫
      homologyMap ((koszulModuleFunctor z).map f) (i - (e : ℤ)) at h
  simpa only [koszulLinearDualHomologyNatIso_app] using h

/-- Coefficient zero maps can be transferred in either direction across Koszul self-duality. -/
lemma koszulLinearDualHomology_map_eq_zero_iff {e : ℕ} (z : Fin e → R)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (i : ℤ) :
    homologyMap ((cochainLinearDualFunctor (koszulComplex z)).map f) i = 0 ↔
      homologyMap ((koszulModuleFunctor z).map f) (i - (e : ℤ)) = 0 := by
  have h := koszulLinearDualHomologyIso_naturality z f i
  constructor
  · intro hf
    apply (cancel_epi (koszulLinearDualHomologyIso z M i).hom).mp
    rw [← h, hf, zero_comp, comp_zero]
  · intro hf
    apply (cancel_mono (koszulLinearDualHomologyIso z N i).hom).mp
    rw [h, hf, comp_zero, zero_comp]

end SerrePositivity
