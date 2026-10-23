module

public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictNerveMaps
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.F1.Coherent.Edges
public import Mathlib.CategoryTheory.Functor.Currying

/-!
概要：通常の自然変換を strictCoherentDiagram 間の実際の単体的ホモトピーへ写す。
方針：自然変換を二頂点の関手とみなし、uncurry した円柱を nerve で写す。
規約：始域は既存の ULift nerve、標的は既存の coherent nerve。
使われ方：HTT 4.2.4.1、Kerodon §4.5.1。fibration 置換した cospan の図式比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra.StrictDiagramTransformation
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]

/-- 自然変換を表す通常の関手円柱。 -/
def cylinder {F G : I ⥤ C} (η : F ⟶ G) : Fin 2 × I ⥤ C :=
  Functor.uncurry.obj (ComposableArrows.mk₁ η)

/-- 自然変換の nerve 上の実際の円柱。 -/
def nerveCylinder {F G : I ⥤ C} (η : F ⟶ G) :
    (SSet.uliftFunctor.{v, u}).obj (nerve I) ⊗ (Δ[1] : SSet.{max u v}) ⟶ nerve C where
  app n := ↾fun z ↦
    (((SimplexCategory.toCat.map (stdSimplex.objEquiv z.2)).toFunctor).prod' z.1.down) ⋙ cylinder η
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro z
    rfl

/-- strict な図式を coherent nerve へ写す円柱。 -/
def map {F G : I ⥤ C} [SimplicialCategory C] (η : F ⟶ G) :
    (SSet.uliftFunctor.{v, u}).obj (nerve I) ⊗ (Δ[1] : SSet.{max u v}) ⟶
      SimplicialNerve C := nerveCylinder η ≫ nerveToCoherent C

/-- 円柱の始点は元の図式。 -/
lemma map_zero {F G : I ⥤ C} [SimplicialCategory C] (η : F ⟶ G) :
    SSet.ι₀ ≫ map η = strictCoherentDiagram F := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s⟩
  apply congrArg ((nerveToCoherent C).app _)
  refine CategoryTheory.Functor.ext (fun i ↦ rfl) (fun i j f ↦ ?_)
  change (𝟙 (F.obj (s.obj i))) ≫ F.map (s.map f) = _
  simp only [Category.id_comp, eqToHom_refl, Category.comp_id]
  rfl

/-- 円柱の終点は比較先の図式。 -/
lemma map_one {F G : I ⥤ C} [SimplicialCategory C] (η : F ⟶ G) :
    SSet.ι₁ ≫ map η = strictCoherentDiagram G := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s⟩
  apply congrArg ((nerveToCoherent C).app _)
  refine CategoryTheory.Functor.ext (fun i ↦ rfl) (fun i j f ↦ ?_)
  change (𝟙 (G.obj (s.obj i))) ≫ G.map (s.map f) = _
  simp only [Category.id_comp, eqToHom_refl, Category.comp_id]
  rfl

/-- 通常の自然変換が与える二つの strict な coherent 図式間のホモトピー。 -/
def homotopy {F G : I ⥤ C} [SimplicialCategory C] (η : F ⟶ G) :
    SSet.Homotopy (strictCoherentDiagram F) (strictCoherentDiagram G) where
  h := map η
  h₀ := map_zero η
  h₁ := map_one η
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    exact False.elim a.property

/-- ホモトピーの各頂点での辺は元の自然変換の成分。 -/
lemma component_edge {F G : I ⥤ C} [SimplicialCategory C] (η : F ⟶ G) (i : I) :
    (simplicialHomotopyVertexEdge (homotopy η) (ULift.up (nerveVertex i))).edge =
      (coherentNerveEdge (η.app i)).edge := by
  change (nerveToCoherent C).app _ _ = (nerveToCoherent C).app _ _
  apply congrArg ((nerveToCoherent C).app _)
  refine ComposableArrows.ext₁ rfl rfl ?_
  change η.app i ≫ G.map (𝟙 i) = _
  simp

/-- 点ごとに可逆な通常の自然変換は、実際の coherent 図式の関手同型を与える。 -/
def functorIso {F G : I ⥤ C} [SimplicialCategory C]
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] (η : F ⟶ G)
    (hη : ∀ i, IsInvertibleEdge (coherentNerveEdge (η.app i))) :
    FunctorIso (strictCoherentDiagram F) (strictCoherentDiagram G) := by
  apply functorIsoOfPointwiseInvertibleHomotopy (homotopy η)
  rintro ⟨s⟩
  have hs : s = nerveVertex (s.obj 0) := ComposableArrows.ext₀ rfl
  rw [hs]
  exact (isInvertibleEdge_congr (component_edge η _)).mpr (hη _)

end SerrePositivity.KST.Spectra.StrictDiagramTransformation
