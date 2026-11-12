module
public import SerrePositivity.KST.SConstruction.BundledDGInput
public import SerrePositivity.KST.SConstruction.DGFunctorNativeCompositionCoherence

/-! # 小さい厳密 dg 入力の実単体的豊穣圏
概要：元の小さい dg 圏を対象、厳密 dg 関手を通常の射、native Kan core を写像空間とする。
方針：元の直積横合成の結合・単位を束ね、零単体と厳密関手の同値で通常の圏と照合する。
規約：対象宇宙を縮めず、非離散な高次入力を保持。使われ方：厳密豊穣 BF K の入力。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の厳密 dg 関手と native Kan 写像空間の零単体の実同値。 -/
def dgFunctorNativeMappingVertexEquiv (D E : Type v) [DGCategory A D] [DGCategory A E]
    [Small.{u} D] : DGFunctor A D E ≃ (dgFunctorNativeMappingSpace A D E).obj (op ⦋0⦌) where
  toFun := dgFunctorNativeMappingVertex A D E
  invFun x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv x.val
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.left_inv x.val

/-- 元の小さい dg 入力の native core による実単体的豊穣構造。 -/
@[instance_reducible]
def smallDGNativeEnrichment :
    EnrichedCategory SSet.{max u v} (SmallBundledDGCategory.{u, v} A) where
  Hom C D := dgFunctorNativeMappingSpace A C D
  id C := dgFunctorNativeIdentity A C
  comp C D E := dgFunctorNativeComposition A C D E
  id_comp C D := by
    change (λ_ (dgFunctorNativeMappingSpace A C D)).inv ≫
      dgFunctorNativeIdentity A C ▷ dgFunctorNativeMappingSpace A C D ≫
      dgFunctorNativeComposition A C C D = 𝟙 _
    rw [← tensorHom_id, dgFunctorNativeComposition_left_unit, Iso.inv_hom_id]
  comp_id C D := by
    change (ρ_ (dgFunctorNativeMappingSpace A C D)).inv ≫
      dgFunctorNativeMappingSpace A C D ◁ dgFunctorNativeIdentity A D ≫
      dgFunctorNativeComposition A C D D = 𝟙 _
    rw [← id_tensorHom, dgFunctorNativeComposition_right_unit, Iso.inv_hom_id]
  assoc C D E F := by
    have h := congrArg
      (fun f => (α_ (dgFunctorNativeMappingSpace A C D) (dgFunctorNativeMappingSpace A D E)
        (dgFunctorNativeMappingSpace A E F)).inv ≫ f)
      (dgFunctorNativeComposition_associativity A C D E F)
    simpa only [tensorHom_id, id_tensorHom, Category.assoc, Iso.inv_hom_id_assoc] using h

/-- 元の厳密 dg 関手と native Kan 写像空間への単位射の実同値。 -/
def smallDGNativeHomEquiv (C D : SmallBundledDGCategory.{u, v} A) :
    DGFunctor A C D ≃ (𝟙_ SSet.{max u v} ⟶ dgFunctorNativeMappingSpace A C D) :=
  (dgFunctorNativeMappingVertexEquiv A C D).trans
    (SSet.unitHomEquiv (dgFunctorNativeMappingSpace A C D)).symm

/-- 単位射との実同値は、元の native 関手頂点を回収する。 -/
lemma smallDGNativeHomEquiv_vertex (C D : SmallBundledDGCategory.{u, v} A)
    (F : DGFunctor A C D) :
    SSet.unitHomEquiv (dgFunctorNativeMappingSpace A C D) (smallDGNativeHomEquiv A C D F) =
      dgFunctorNativeMappingVertex A C D F :=
  (SSet.unitHomEquiv _).apply_symm_apply _

private lemma unitHomEquiv_tensor {X Y Z : SSet.{w}}
    (f : 𝟙_ SSet ⟶ X) (g : 𝟙_ SSet ⟶ Y) (h : X ⊗ Y ⟶ Z) :
    SSet.unitHomEquiv Z ((λ_ (𝟙_ SSet)).inv ≫ (f ⊗ₘ g) ≫ h) =
      h.app (op ⦋0⦌) (SSet.unitHomEquiv X f, SSet.unitHomEquiv Y g) := rfl

/-- 単位射との実同値は、元の厳密 dg 関手合成を全単体の実横合成で回収する。 -/
lemma smallDGNativeHomEquiv_comp (C D E : SmallBundledDGCategory.{u, v} A)
    (F : DGFunctor A C D) (G : DGFunctor A D E) :
    smallDGNativeHomEquiv A C E (DGFunctor.comp F G) =
      (λ_ (𝟙_ SSet.{max u v})).inv ≫
        (smallDGNativeHomEquiv A C D F ⊗ₘ smallDGNativeHomEquiv A D E G) ≫
        dgFunctorNativeComposition A C D E := by
  apply (SSet.unitHomEquiv (dgFunctorNativeMappingSpace A C E)).injective
  rw [smallDGNativeHomEquiv_vertex, unitHomEquiv_tensor,
    smallDGNativeHomEquiv_vertex, smallDGNativeHomEquiv_vertex]
  exact (dgFunctorNativeComposition_vertex A C D E F G).symm

/-- 元の厳密 dg 関手を通常の射に保つ、小さい dg 入力の実単体的圏。 -/
instance smallBundledDGNativeSimplicialCategory :
    SimplicialCategory (SmallBundledDGCategory.{u, v} A) where
  toEnrichedCategory := smallDGNativeEnrichment A
  homEquiv {C D} := smallDGNativeHomEquiv A C D
  homEquiv_id _C := rfl
  homEquiv_comp {C D E} F G := smallDGNativeHomEquiv_comp A C D E F G

/-- 小さい dg 入力の実単体的写像空間は全て Kan 複体。 -/
instance smallBundledDGNativeHom_kan (C D : SmallBundledDGCategory.{u, v} A) :
    KanComplex (SimplicialCategory.sHom C D) := by
  change KanComplex (dgFunctorNativeMappingSpace A C D)
  infer_instance

end SerrePositivity.KST.SConstruction
