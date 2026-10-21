module
public import SerrePositivity.KST.SConstruction.PerfDGInput
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGNativeParameterCoherence
public import SerrePositivity.KST.SConstruction.SmallDGNativeSimplicialCategory

/-! # 出力宇宙での厳密 dg 入力の実単体的圏
概要：元の厳密 dg 関手の ULift を通常の射、全 native Kan 関手族の ULift を Hom とする。
方針：検証済みの持ち上げた入力合成と単位を束ね、零単体で元の関手合成を回収する。
規約：通常の射も全高次入力も保持。使われ方：実 Perf の厳密豊穣関手と γ1。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の厳密 dg 関手の ULift と、同じ入力の Kan 写像空間の零単体の実同値。 -/
def perfDGInputVertexEquiv (C D : PerfDGInput.{u, v} A) :
    (C ⟶ D) ≃ (presentedPerfectDGNativeParameter A C D).obj (op ⦋0⦌) where
  toFun F := ULift.up (dgFunctorNativeMappingVertex A C D F.down)
  invFun x := ULift.up ((dgFunctorNativeMappingVertexEquiv A C D).symm x.down)
  left_inv F := ULift.ext ((dgFunctorNativeMappingVertexEquiv A C D).left_inv F.down)
  right_inv x := ULift.ext ((dgFunctorNativeMappingVertexEquiv A C D).right_inv x.down)

/-- 持ち上げた実 Kan 入力の合成・単位による、出力宇宙の豊穣構造。 -/
@[instance_reducible]
def perfDGInputNativeEnrichment :
    EnrichedCategory SSet.{max (u + 1) v} (PerfDGInput.{u, v} A) where
  Hom C D := presentedPerfectDGNativeParameter A C D
  id C := presentedPerfectDGNativeParameterPoint A C C (DGFunctor.id C)
  comp C D E := presentedPerfectDGNativeParameterComp A C D E
  id_comp C D := by
    change (λ_ (presentedPerfectDGNativeParameter A C D)).inv ≫
      presentedPerfectDGNativeParameterPoint A C C (DGFunctor.id C) ▷
        presentedPerfectDGNativeParameter A C D ≫
        presentedPerfectDGNativeParameterComp A C C D = 𝟙 _
    rw [← tensorHom_id, presentedPerfectDGNativeParameterComp_left_unit, Iso.inv_hom_id]
  comp_id C D := by
    change (ρ_ (presentedPerfectDGNativeParameter A C D)).inv ≫
      presentedPerfectDGNativeParameter A C D ◁
        presentedPerfectDGNativeParameterPoint A D D (DGFunctor.id D) ≫
        presentedPerfectDGNativeParameterComp A C D D = 𝟙 _
    rw [← id_tensorHom, presentedPerfectDGNativeParameterComp_right_unit, Iso.inv_hom_id]
  assoc C D E F := by
    have h := congrArg
      (fun f => (α_ (presentedPerfectDGNativeParameter A C D)
        (presentedPerfectDGNativeParameter A D E)
        (presentedPerfectDGNativeParameter A E F)).inv ≫ f)
      (presentedPerfectDGNativeParameterComp_associativity A C D E F)
    simpa only [tensorHom_id, id_tensorHom, Category.assoc, Iso.inv_hom_id_assoc] using h

/-- 元の通常の射と、同じ native Kan 写像空間への単位射の実同値。 -/
def perfDGInputUnitHomEquiv (C D : PerfDGInput.{u, v} A) :
    (C ⟶ D) ≃ (𝟙_ SSet.{max (u + 1) v} ⟶ presentedPerfectDGNativeParameter A C D) :=
  (perfDGInputVertexEquiv A C D).trans
    (SSet.unitHomEquiv (presentedPerfectDGNativeParameter A C D)).symm

/-- 通常の射と単位射の同値は、元の同じ厳密 dg 関手の点を回収する。 -/
lemma perfDGInputUnitHomEquiv_point (C D : PerfDGInput.{u, v} A) (F : C ⟶ D) :
    perfDGInputUnitHomEquiv A C D F = presentedPerfectDGNativeParameterPoint A C D F.down := rfl

/-- 単位射との実同値は、元の持ち上げた関手頂点を回収する。 -/
lemma perfDGInputUnitHomEquiv_vertex (C D : PerfDGInput.{u, v} A) (F : C ⟶ D) :
    SSet.unitHomEquiv (presentedPerfectDGNativeParameter A C D) (perfDGInputUnitHomEquiv A C D F) =
      ULift.up (dgFunctorNativeMappingVertex A C D F.down) :=
  (SSet.unitHomEquiv _).apply_symm_apply _

private lemma unitHomEquiv_tensor {X Y Z : SSet.{w}}
    (f : 𝟙_ SSet ⟶ X) (g : 𝟙_ SSet ⟶ Y) (h : X ⊗ Y ⟶ Z) :
    SSet.unitHomEquiv Z ((λ_ (𝟙_ SSet)).inv ≫ (f ⊗ₘ g) ≫ h) =
      h.app (op ⦋0⦌) (SSet.unitHomEquiv X f, SSet.unitHomEquiv Y g) := rfl

/-- 通常の射と単位射の実同値は、元の厳密 dg 関手合成を回収する。 -/
lemma perfDGInputUnitHomEquiv_comp (C D E : PerfDGInput.{u, v} A) (F : C ⟶ D) (G : D ⟶ E) :
    perfDGInputUnitHomEquiv A C E (F ≫ G) =
      (λ_ (𝟙_ SSet.{max (u + 1) v})).inv ≫
        (perfDGInputUnitHomEquiv A C D F ⊗ₘ perfDGInputUnitHomEquiv A D E G) ≫
        presentedPerfectDGNativeParameterComp A C D E := by
  apply (SSet.unitHomEquiv (presentedPerfectDGNativeParameter A C E)).injective
  rw [perfDGInputUnitHomEquiv_vertex, unitHomEquiv_tensor,
    perfDGInputUnitHomEquiv_vertex, perfDGInputUnitHomEquiv_vertex]
  apply ULift.ext
  exact (dgFunctorNativeComposition_vertex A C D E F.down G.down).symm

/-- 元の通常の射を保つ、出力宇宙での厳密 dg 入力の実単体的圏。 -/
instance perfDGInputSimplicialCategory : SimplicialCategory (PerfDGInput.{u, v} A) where
  toEnrichedCategory := perfDGInputNativeEnrichment A
  homEquiv {C D} := perfDGInputUnitHomEquiv A C D
  homEquiv_id _C := rfl
  homEquiv_comp {C D E} F G := perfDGInputUnitHomEquiv_comp A C D E F G

/-- 出力宇宙での元の全 native 入力写像空間は Kan 複体。 -/
instance perfDGInputHom_kan (C D : PerfDGInput.{u, v} A) :
    KanComplex (SimplicialCategory.sHom C D) := by
  change KanComplex (presentedPerfectDGNativeParameter A C D)
  infer_instance

end SerrePositivity.KST.SConstruction
