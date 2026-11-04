module
public import SerrePositivity.HomologicalAlgebra.Complex.Cone
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Tower

/-! # Base change respects the actual multiplicative Koszul maps -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HomologicalComplex.homotopyCofiber DerivedCompletion
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

private lemma coneArrowIso_cast
    {P Q P' Q' : CochainComplex (ModuleCat.{u} S) ℤ}
    (f f' : P ⟶ Q) (g : P' ⟶ Q') (h : f = f')
    (eP : P ≅ P') (eQ : Q ≅ Q') (w : eP.hom ≫ g = f' ≫ eQ.hom) :
    Eq.mpr (congrArg (fun t => homotopyCofiber t ≅ homotopyCofiber g) h)
        (mapArrowIso f' g (fun j => ⟨j - 1, by simp⟩) (Arrow.isoMk eP eQ w)) =
      mapArrowIso f g (fun j => ⟨j - 1, by simp⟩)
        (Arrow.isoMk eP eQ (by rw [h]; exact w)) := by
  cases h
  rfl

/-- The canonical Koszul base-change isomorphism respects coordinatewise
multiplication maps, hence not only individual Koszul objects. -/
lemma baseChangeKoszulIso_mapOfMul : ∀ {e : ℕ} (a b c : Fin e → R)
    (h : ∀ i, a i = b i * c i),
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
        (koszulComplexMapOfMul R a b c h) ≫ (baseChangeKoszulIso φ b).hom =
      (baseChangeKoszulIso φ a).hom ≫
        koszulComplexMapOfMul S (φ ∘ a) (φ ∘ b) (φ ∘ c)
          (fun i => by simp only [Function.comp_apply, h, map_mul]) := by
  intro e
  induction e with
  | zero =>
    intro a b c h
    have hb : b = a := Subsingleton.elim _ _
    subst b
    change _ = (baseChangeKoszulIso φ a).hom ≫ 𝟙 _
    change ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (.up ℤ)).map
      (𝟙 _) ≫ (baseChangeKoszulIso φ a).hom = (baseChangeKoszulIso φ a).hom
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  | succ e ih =>
    intro a b c h
    simp only [koszulComplexMapOfMul, baseChangeKoszulIso, id_eq, Iso.trans_hom]
    rw [← Category.assoc, cochainConeAdditiveIso_hom_naturality]
    simp only [Category.assoc]
    apply (cancel_epi (mapHomologicalComplexObjIso
      (smulId (a (Fin.last e)) (koszulComplex (Fin.init a)))
      (ModuleCat.extendScalars.{u, u, u} φ)).hom).mpr
    rw [coneArrowIso_cast
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
        (smulId (b (Fin.last e)) (koszulComplex (Fin.init b))))
      (smulId (φ (b (Fin.last e))) (baseChange φ (koszulComplex (Fin.init b))))
      (smulId (φ (b (Fin.last e))) (koszulComplex (Fin.init (φ ∘ b))))
      (baseChange_smulId φ _ _) (baseChangeKoszulIso φ (Fin.init b))
      (baseChangeKoszulIso φ (Fin.init b)) (by simp [smulId])]
    rw [coneArrowIso_cast
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
        (smulId (a (Fin.last e)) (koszulComplex (Fin.init a))))
      (smulId (φ (a (Fin.last e))) (baseChange φ (koszulComplex (Fin.init a))))
      (smulId (φ (a (Fin.last e))) (koszulComplex (Fin.init (φ ∘ a))))
      (baseChange_smulId φ _ _) (baseChangeKoszulIso φ (Fin.init a))
      (baseChangeKoszulIso φ (Fin.init a)) (by simp [smulId])]
    simp only [mapArrowIso_hom]
    erw [← mapArrowHom_comp, ← mapArrowHom_comp]
    congr 1
    apply Arrow.hom_ext
    · change ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
          (c (Fin.last e) • koszulComplexMapOfMul R (Fin.init a) (Fin.init b) (Fin.init c)
            (fun i => h i.castSucc)) ≫ (baseChangeKoszulIso φ (Fin.init b)).hom =
        (baseChangeKoszulIso φ (Fin.init a)).hom ≫
          (φ (c (Fin.last e)) • koszulComplexMapOfMul S (φ ∘ Fin.init a)
            (φ ∘ Fin.init b) (φ ∘ Fin.init c) _)
      rw [extendScalars_mapHomologicalComplex_smul, Linear.smul_comp, Linear.comp_smul,
        ih (Fin.init a) (Fin.init b) (Fin.init c) (fun i => h i.castSucc)]
    · exact ih (Fin.init a) (Fin.init b) (Fin.init c) (fun i => h i.castSucc)

/-- Coordinate equalities transport actual multiplication maps without changing them. -/
lemma koszulComplexMapOfMul_congr {e : ℕ} (a b c a' b' c' : Fin e → S)
    (h : ∀ i, a i = b i * c i) (h' : ∀ i, a' i = b' i * c' i)
    (ha : a = a') (hb : b = b') (hc : c = c') :
    eqToHom (congrArg koszulComplex ha) ≫ koszulComplexMapOfMul S a' b' c' h' =
      koszulComplexMapOfMul S a b c h ≫ eqToHom (congrArg koszulComplex hb) := by
  subst a'
  subst b'
  subst c'
  simp

/-- The existing base-change isomorphism normalized to the literal power tower
of the images of the coordinates. -/
def baseChangePowerKoszulIso {e : ℕ} (z : Fin e → R) (n : ℕ) :
    baseChange φ (powerKoszulTower R z n) ≅ powerKoszulTower S (φ ∘ z) n :=
  baseChangeKoszulIso φ (fun i => z i ^ n) ≪≫
    eqToIso (congrArg koszulComplex (funext (fun i => map_pow φ (z i) n)))

/-- Base change respects the actual adjacent power transitions, with no
flatness or regular-sequence hypothesis. -/
@[reassoc]
lemma baseChangePowerKoszulIso_transition {e : ℕ} (z : Fin e → R) (n : ℕ) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
        (powerKoszulTransition R z n) ≫ (baseChangePowerKoszulIso φ z n).hom =
      (baseChangePowerKoszulIso φ z (n + 1)).hom ≫
        powerKoszulTransition S (φ ∘ z) n := by
  let a : Fin e → R := fun i => z i ^ (n + 1)
  let b : Fin e → R := fun i => z i ^ n
  let h : ∀ i, a i = b i * z i := fun i => pow_succ (z i) n
  change ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
      (koszulComplexMapOfMul R a b z h) ≫ ((baseChangeKoszulIso φ b).hom ≫ _) =
    ((baseChangeKoszulIso φ a).hom ≫ _) ≫ _
  rw [← Category.assoc, baseChangeKoszulIso_mapOfMul φ a b z h, Category.assoc,
    Category.assoc]
  apply congrArg ((baseChangeKoszulIso φ a).hom ≫ ·)
  exact (koszulComplexMapOfMul_congr (S := S)
    (φ ∘ a) (φ ∘ b) (φ ∘ z)
    (fun i => (φ (z i)) ^ (n + 1)) (fun i => (φ (z i)) ^ n) (φ ∘ z)
    (fun i => by simp only [Function.comp_apply, h, map_mul])
    (fun i => pow_succ _ _) (funext (fun i => map_pow φ (z i) (n + 1)))
    (funext (fun i => map_pow φ (z i) n)) rfl).symm

end SerrePositivity
