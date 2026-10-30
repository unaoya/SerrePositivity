module
public import SerrePositivity.DifferentialGraded.Perfect.RingDerivedFiniteCover
public import SerrePositivity.CategoryTheory.Triangulated.Padding

/-! # retractと補対象の三角形を有限射影複体上のconeで表す -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex Pretriangulated
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma ringDerivedRetract_complement {X Y : DerivedCategory (ModuleCat.{u} A)} (a : Retract X Y) :
    ∃ (Z : DerivedCategory (ModuleCat.{u} A)) (e : Y ≅ X ⊞ Z), a.i ≫ e.hom = biprod.inl := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle a.i
  let T := Triangle.mk a.i g h
  obtain ⟨e, he, _⟩ := exists_iso_binaryBiproduct_of_distTriang T hT
    (T.mor₃_eq_zero_of_mono₁ hT (show Mono a.i from inferInstance))
  exact ⟨Z, e, he⟩

lemma ringDerived_chainMap_homology_epi {P K : Complex A} (f : P ⟶ K) (n : ℤ)
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map (DerivedCategory.Q.map f))] :
    Epi (homologyMap f n) := by
  let e := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n
  have hn : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
      (DerivedCategory.Q.map f) ≫ e.hom.app K = e.hom.app P ≫ homologyMap f n :=
    e.hom.naturality f
  have : Epi (e.hom.app P ≫ homologyMap f n) := by
    rw [← hn]
    infer_instance
  exact epi_of_epi (e.hom.app P) _

lemma ringDerived_homology_biprodMap_epi (n : ℤ)
    {X Y Z W : DerivedCategory (ModuleCat.{u} A)} (f : X ⟶ Y) (g : Z ⟶ W)
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map f)]
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map g)] :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map (biprod.map f g)) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) n
  let : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
  have he : H.map (biprod.map f g) = (H.mapBiprod X Z).hom ≫
      biprod.map (H.map f) (H.map g) ≫ (H.mapBiprod Y W).inv := by
    apply (cancel_mono (H.mapBiprod Y W).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply biprod.hom_ext
    all_goals simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst,
      biprod.lift_snd, biprod.lift_fst_assoc, biprod.lift_snd_assoc,
      biprod.map_fst, biprod.map_snd, ← H.map_comp]
  rw [he]
  infer_instance

lemma ringDerivedTriangle_sum_coneRetract
    (T U : Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ distTriang _) (hU : U ∈ distTriang _)
    (F : ModuleCat.{u} A) [Module.Finite A F] [Module.Projective A F]
    (P : Complex A) (b : ℤ)
    (e₁ : DerivedCategory.Q.obj ((single (ModuleCat.{u} A) (.up ℤ) b).obj F) ≅ T.obj₁ ⊞ U.obj₁)
    (e₂ : DerivedCategory.Q.obj P ≅ T.obj₂ ⊞ U.obj₂)
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) b).map T.mor₁)]
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) b).map U.mor₁)] :
    ∃ f : (single (ModuleCat.{u} A) (.up ℤ) b).obj F ⟶ P,
      Epi (homologyMap f b) ∧ Nonempty (Retract T.obj₃ (DerivedCategory.Q.obj
        (CochainComplex.mappingCone f))) := by
  let S := (single (ModuleCat.{u} A) (.up ℤ) b).obj F
  let h := e₁.hom ≫ biprod.map T.mor₁ U.mor₁ ≫ e₂.inv
  obtain ⟨f, hf⟩ := ringComplexDerived_map_surjective A S
    (strictlyPerfectComplex_single A F b) P h
  let V := triangleBiproduct T U
  let C := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)
  let e : C ≅ V := isoTriangleOfIso₁₂ C V (DerivedCategory.mappingCone_triangle_distinguished f)
    (triangleBiproduct_distinguished T U hT hU) e₁ e₂ (by
      change DerivedCategory.Q.map f ≫ e₂.hom = e₁.hom ≫ biprod.map T.mor₁ U.mor₁
      rw [hf]
      simp only [h, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  let r : Retract T.obj₃ V.obj₃ :=
    { i := biprod.inl, r := biprod.fst, retract := biprod.inl_fst }
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) b
  have : Epi (H.map (DerivedCategory.Q.map f)) := by
    let := ringDerived_homology_biprodMap_epi A b T.mor₁ U.mor₁
    rw [hf]
    simp only [h, H.map_comp]
    infer_instance
  exact ⟨f, ringDerived_chainMap_homology_epi A f b,
    ⟨r.trans (Retract.ofIso (Triangle.π₃.mapIso e).symm)⟩⟩

end SerrePositivity.DifferentialGraded
