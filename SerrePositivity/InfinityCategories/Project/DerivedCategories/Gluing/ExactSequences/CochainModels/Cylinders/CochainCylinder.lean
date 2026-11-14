module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.ComplexQuasiIsoSpan

/-! 指定した比較 cochain を同じ二端を持つ複体の円柱からの鎖写像へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] (K : Complex R)

def dgGluingCochainCylinder : Complex R := K ⊞ mappingCone (𝟙 K)

def dgGluingCochainCylinderProjection : dgGluingCochainCylinder K ⟶ K := biprod.fst

def dgGluingCochainCylinderZero : K ⟶ dgGluingCochainCylinder K := biprod.inl

def dgGluingCochainCylinderOne : K ⟶ dgGluingCochainCylinder K :=
  biprod.lift (𝟙 K) (mappingCone.inr (𝟙 K))

lemma dgGluingCochainCylinderZero_projection :
    dgGluingCochainCylinderZero K ≫ dgGluingCochainCylinderProjection K = 𝟙 K :=
  biprod.inl_fst

lemma dgGluingCochainCylinderOne_projection :
    dgGluingCochainCylinderOne K ≫ dgGluingCochainCylinderProjection K = 𝟙 K :=
  biprod.lift_fst _ _

def dgGluingCochainCylinderHomotopyEquiv : HomotopyEquiv (dgGluingCochainCylinder K) K where
  hom := dgGluingCochainCylinderProjection K
  inv := dgGluingCochainCylinderZero K
  homotopyHomInvId := by
    let hc : Homotopy (𝟙 (mappingCone (𝟙 K))) 0 :=
      mappingCone.liftHomotopy _ _ _ (mappingCone.snd _) 0 (by simp) (by simp)
    let h := (hc.compRight
      (biprod.inr : mappingCone (𝟙 K) ⟶ dgGluingCochainCylinder K)).compLeft
        (biprod.snd : dgGluingCochainCylinder K ⟶ mappingCone (𝟙 K))
    have h' : Homotopy
        (biprod.fst ≫ biprod.inl : dgGluingCochainCylinder K ⟶ dgGluingCochainCylinder K)
        (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) := by
      simpa only [Category.comp_id, Category.id_comp, Category.assoc, comp_zero, zero_comp,
        add_zero] using (Homotopy.add (Homotopy.refl
        (biprod.fst ≫ biprod.inl : dgGluingCochainCylinder K ⟶ dgGluingCochainCylinder K)) h).symm
    exact h'.trans (Homotopy.ofEq (biprod.total (X := K) (Y := mappingCone (𝟙 K))))
  homotopyInvHomId := Homotopy.ofEq (dgGluingCochainCylinderZero_projection K)

lemma dgGluingCochainCylinderProjection_quasiIso :
    QuasiIso (dgGluingCochainCylinderProjection K) :=
  (dgGluingCochainCylinderHomotopyEquiv K).quasiIso_hom

lemma dgGluingCochainCylinderProjection_surjective (k : ℤ) :
    Function.Surjective ((dgGluingCochainCylinderProjection K).f k) := by
  intro z
  refine ⟨(dgGluingCochainCylinderZero K).f k z, ?_⟩
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (dgGluingCochainCylinderZero_projection K) k) z

variable {K} {L : Complex R} (f g : K ⟶ L) (h : Cochain K L (-1))
  (he : δ (-1) 0 h = Cochain.ofHom (g - f))

def dgGluingCochainCylinderExtension : dgGluingCochainCylinder K ⟶ L :=
  biprod.desc f (mappingCone.desc (𝟙 K) h (g - f) (by
    simpa only [Category.id_comp] using he))

lemma dgGluingCochainCylinderExtension_zero :
    dgGluingCochainCylinderZero K ≫ dgGluingCochainCylinderExtension f g h he = f :=
  biprod.inl_desc _ _

lemma dgGluingCochainCylinderExtension_one :
    dgGluingCochainCylinderOne K ≫ dgGluingCochainCylinderExtension f g h he = g := by
  dsimp only [dgGluingCochainCylinderOne, dgGluingCochainCylinderExtension]
  rw [biprod.lift_desc, Category.id_comp, mappingCone.inr_desc]
  abel

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
