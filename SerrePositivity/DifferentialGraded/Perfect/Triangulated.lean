module
public import SerrePositivity.DifferentialGraded.Perfect.KaroubiCriterion
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveDerivedLifting
public import SerrePositivity.DifferentialGraded.Derived.ConeTriangles
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # finite cellの導来本質像の三角閉性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance derivedFiniteCellOverClosedUnderIso (S : Set D) :
    (derivedFiniteCellOver A D S).IsClosedUnderIsomorphisms := by
  dsimp [derivedFiniteCellOver]
  infer_instance

lemma derivedFiniteCellOver_triangle_obj₃ (S : Set D)
    (T : Triangle (DerivedModuleCategory A D)) (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (h₁ : derivedFiniteCellOver A D S T.obj₁) (h₂ : derivedFiniteCellOver A D S T.obj₂) :
    derivedFiniteCellOver A D S T.obj₃ := by
  obtain ⟨M, hM, ⟨eM⟩⟩ := h₁
  obtain ⟨N, hN, ⟨eN⟩⟩ := h₂
  obtain ⟨f, hf⟩ := moduleProjectiveToDerived_map_surjective A D
    (moduleFiniteCellOver_homotopicallyProjective A D hM) (eM.hom ≫ T.mor₁ ≫ eN.inv)
  have he : Arrow.mk (moduleDerivedConeTriangle A D f).mor₁ ≅ Arrow.mk T.mor₁ :=
    Arrow.isoMk eM eN (by
      change eM.hom ≫ T.mor₁ = (moduleToDerived A D).map f ≫ eN.hom
      rw [hf]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  obtain ⟨e, _⟩ := exists_iso_of_arrow_iso (moduleDerivedConeTriangle A D f) T
    (moduleDerivedConeTriangle_distinguished A D f) hT he
  exact ⟨moduleCone A D f, moduleFiniteCellOver_cone A D hM hN f,
    ⟨Triangle.π₃.mapIso e⟩⟩

instance derivedFiniteCellOverTriangulatedClosed₃ (S : Set D) :
    (derivedFiniteCellOver A D S).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (derivedFiniteCellOver_triangle_obj₃ A D S)

instance derivedFiniteCellOverTriangulatedClosed₂ (S : Set D) :
    (derivedFiniteCellOver A D S).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

instance derivedFiniteCellOverContainsZero (S : Set D) :
    (derivedFiniteCellOver A D S).ContainsZero := by
  have : (moduleToDerived A D).Additive := Functor.additive_of_iso (moduleToHomotopyDerivedIso A D)
  exact ⟨⟨(moduleToDerived A D).obj (moduleZero A D),
    (moduleToDerived A D).map_isZero (moduleZero_isZero A D),
    (moduleFiniteCellOver A D S).prop_map_obj (moduleToDerived A D)
      (moduleFiniteCellOver_zero A D S)⟩⟩

instance derivedFiniteCellOverIsTriangulated (S : Set D) :
    (derivedFiniteCellOver A D S).IsTriangulated := by
  constructor

lemma modulePerfectOver_triangle_obj₂ (S : Set D)
    (T : Triangle (DerivedModuleCategory A D)) (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (h₁ : modulePerfectOver A D S T.obj₁) (h₃ : modulePerfectOver A D S T.obj₃) :
    modulePerfectOver A D S T.obj₂ := by
  let P := derivedFiniteCellOver A D S
  have hp : ObjectProperty.extensionProduct P P ≤ P :=
    ObjectProperty.extensionProduct_le_of_isTriangulatedClosed₂ (le_refl P) (le_refl P)
  have hc : ObjectProperty.extensionProduct P.retractClosure P.retractClosure ≤ P.retractClosure :=
    (ObjectProperty.extensionProduct_retractClosure_retractClosure_le P P).trans
      (ObjectProperty.monotone_retractClosure hp)
  exact hc _ ⟨T.obj₁, T.obj₃, T.mor₁, T.mor₂, T.mor₃, hT, h₁, h₃⟩

instance modulePerfectOverTriangulatedClosed₂ (S : Set D) :
    (modulePerfectOver A D S).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (modulePerfectOver_triangle_obj₂ A D S)

instance modulePerfectOverIsTriangulated (S : Set D) :
    (modulePerfectOver A D S).IsTriangulated := by
  constructor

instance modulePerfectIsTriangulated : (modulePerfect A D).IsTriangulated :=
  modulePerfectOverIsTriangulated A D Set.univ

instance derivedFiniteCellInclusionIsTriangulated (S : Set D) :
    (derivedFiniteCellInclusion A D S).IsTriangulated := by
  dsimp [derivedFiniteCellInclusion]
  infer_instance

instance perfectModuleInclusionIsTriangulated (S : Set D) :
    (perfectModuleInclusion A D S).IsTriangulated := by
  dsimp [perfectModuleInclusion]
  infer_instance

instance finiteCellKaroubiFunctorIsTriangulated (S : Set D) :
    (finiteCellKaroubiFunctor A D S).IsTriangulated := by
  dsimp [finiteCellKaroubiFunctor]
  infer_instance

end SerrePositivity.DifferentialGraded
