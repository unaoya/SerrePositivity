module
public import SerrePositivity.DifferentialGraded.Endomorphism.EssentialImageShift

/-! # 再構成比較の本質的像のdistinguished triangle閉性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)
include hgen

lemma perfectEndomorphismEssentialImage_triangle_obj₃
    (T : Triangle (DerivedModuleCategory A (EndomorphismObject E.val)))
    (hT : T ∈ distTriang _)
    (h₁ : (perfectEndomorphismHomToDerived A D S E).essImage T.obj₁)
    (h₂ : (perfectEndomorphismHomToDerived A D S E).essImage T.obj₂) :
    (perfectEndomorphismHomToDerived A D S E).essImage T.obj₃ := by
  let G := perfectEndomorphismHomToDerived A D S E
  let R := endomorphismDerivedHom A D E.val E.property.1
  let Q := moduleToDerived A (EndomorphismObject E.val)
  have : G.Full := perfectEndomorphismHomToDerived_full A D S E hgen
  obtain ⟨X₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨X₂, ⟨e₂⟩⟩ := h₂
  obtain ⟨q, hq⟩ := G.map_surjective (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
  let P₁ := moduleCanonicalProjectiveResolution A D X₁.obj.as.obj
  let P₂ := moduleCanonicalProjectiveResolution A D X₂.obj.as.obj
  let c₁ : (moduleToDerived A D).obj P₁.obj ≅ X₁.obj := moduleDerivedIso A D P₁.π P₁.quasiIso
  let c₂ : (moduleToDerived A D).obj P₂.obj ≅ X₂.obj := moduleDerivedIso A D P₂.π P₂.quasiIso
  obtain ⟨f, hf⟩ := moduleProjectiveToDerived_map_surjective A D P₁.projective
    (c₁.hom ≫ q.hom ≫ c₂.inv)
  let r₁ := (endomorphismDerivedHomComputation A D E.val E.property.1 P₁.obj).symm ≪≫ R.mapIso c₁
  let r₂ := (endomorphismDerivedHomComputation A D E.val E.property.1 P₂.obj).symm ≪≫ R.mapIso c₂
  have hfac : (moduleToDerived A D).map f ≫ c₂.hom = c₁.hom ≫ q.hom := by
    rw [hf]
    simp only [Category.assoc, c₂.inv_hom_id, Category.comp_id]
  have hmap := congrArg R.map hfac
  simp only [CategoryTheory.Functor.map_comp] at hmap
  have hr : Q.map ((endomorphismModuleHom A D E.val).onClosed.map f) ≫ r₂.hom =
      r₁.hom ≫ R.map q.hom := by
    have hn := congrArg (fun k => k ≫ R.map c₂.hom)
      (endomorphismDerivedHomComputation_inv_naturality A D E.val E.property.1 f)
    have hc := congrArg (fun k =>
      (endomorphismDerivedHomComputation A D E.val E.property.1 P₁.obj).inv ≫ k) hmap
    simp only [Category.assoc] at hn hc
    exact (hn.trans hc).trans (Category.assoc _ _ _).symm
  have hq' : R.map q.hom = e₁.hom ≫ T.mor₁ ≫ e₂.inv := hq
  let he : Arrow.mk (moduleDerivedConeTriangle A (EndomorphismObject E.val)
      ((endomorphismModuleHom A D E.val).onClosed.map f)).mor₁ ≅ Arrow.mk T.mor₁ :=
    Arrow.isoMk (r₁ ≪≫ e₁) (r₂ ≪≫ e₂) (by
      change (r₁.hom ≫ e₁.hom) ≫ T.mor₁ =
        Q.map ((endomorphismModuleHom A D E.val).onClosed.map f) ≫ (r₂.hom ≫ e₂.hom)
      rw [← Category.assoc _ r₂.hom e₂.hom, hr, hq']
      simp only [Category.assoc, e₂.inv_hom_id, Category.comp_id])
  obtain ⟨et, _⟩ := exists_iso_of_arrow_iso
    (moduleDerivedConeTriangle A (EndomorphismObject E.val)
      ((endomorphismModuleHom A D E.val).onClosed.map f)) T
    (moduleDerivedConeTriangle_distinguished A (EndomorphismObject E.val)
      ((endomorphismModuleHom A D E.val).onClosed.map f)) hT he
  have hp₁ := (modulePerfectOver A D S).prop_of_iso c₁.symm X₁.property
  have hp₂ := (modulePerfectOver A D S).prop_of_iso c₂.symm X₂.property
  have hcone := (modulePerfectOver A D S).ext_of_isTriangulatedClosed₃'
    (moduleDerivedConeTriangle A D f) (moduleDerivedConeTriangle_distinguished A D f) hp₁ hp₂
  rw [ObjectProperty.isoClosure_eq_self] at hcone
  refine ⟨⟨(moduleToDerived A D).obj (moduleCone A D f), hcone⟩, ⟨?_⟩⟩
  exact ((Q.mapIso (dgModuleFunctorConeIso A D (EndomorphismObject E.val)
      (endomorphismModuleHom A D E.val) f)) ≪≫
    (endomorphismDerivedHomComputation A D E.val E.property.1 (moduleCone A D f)).symm).symm ≪≫
      Triangle.π₃.mapIso et

lemma perfectEndomorphismEssentialImageTriangulatedClosed₃ :
    (perfectEndomorphismHomToDerived A D S E).essImage.IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk'
    (perfectEndomorphismEssentialImage_triangle_obj₃ A D S E hgen)

lemma perfectEndomorphismEssentialImageTriangulatedClosed₂ :
    (perfectEndomorphismHomToDerived A D S E).essImage.IsTriangulatedClosed₂ := by
  have := perfectEndomorphismEssentialImageTriangulatedClosed₃ A D S E hgen
  exact ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

end SerrePositivity.DifferentialGraded
