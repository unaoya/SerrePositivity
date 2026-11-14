module

public import SerrePositivity.KST.Spectra.EnrichedOrderedCylinderBridge
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedParameterCylinderEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ArrowData

/-!
概要：厳密な単体的自然変換を coherent nerve の実際の区間族へ移す。
方針：単位パラメータの豊穣円柱を、既存の順序付き円柱の pairing で評価する。
規約：入力は全 Hom 上の豊穣自然性。使われ方：Sp の逆関手経路の API 評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.StrictEnrichedTransformation

variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]
  (F G : EnrichedFunctor SSet.{u} C D)
  (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)

/-- 厳密な豊穣自然変換の二段の円柱上の関手。 -/
def cylinder : EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin 2) C) D :=
  (EnrichedOrderedCylinder.bridge (𝟙 (𝟙_ SSet.{u}))).comp SSet
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluationFunctor (𝟙_ SSet.{u}) F G η)

/-- 円柱の左端は元の関手。 -/
lemma cylinder_source :
    (EnrichedOrderedCylinder.stageInclusion (C := C) (0 : Fin 2)).comp SSet
      (cylinder F G η) = F := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  change (𝟙 _ ≫ F.map X Y) ≫ 𝟙 _ = F.map X Y
  simp

/-- 円柱の右端は元の関手。 -/
lemma cylinder_target :
    (EnrichedOrderedCylinder.stageInclusion (C := C) (1 : Fin 2)).comp SSet
      (cylinder F G η) = G := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  change (𝟙 _ ≫ G.map X Y) ≫ 𝟙 _ = G.map X Y
  simp

/-- 指定した厳密な自然変換の全高次単体を保持する区間族。 -/
def family : SimplicialNerve C ⊗ (Δ[1] : SSet.{max u v}) ⟶ SimplicialNerve D :=
  EnrichedOrderedCylinder.nerveSimplexFamily 1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (cylinder F G η)

/-- 区間族の始点は元の関手の coherent nerve。 -/
lemma family_source :
    lift (𝟙 (SimplicialNerve C)) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
      family F G η = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F := by
  rw [family, ← Category.assoc, EnrichedOrderedCylinder.nerveSimplexFamily_vertex,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, cylinder_source]

/-- 区間族の終点は元の関手の coherent nerve。 -/
lemma family_target :
    lift (𝟙 (SimplicialNerve C)) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
      family F G η = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap G := by
  rw [family, ← Category.assoc, EnrichedOrderedCylinder.nerveSimplexFamily_vertex,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, cylinder_target]

/-- 厳密な豊穣自然変換は、元の二つの ∞ 関手を結ぶ実際の自然変換を与える。 -/
def homotopy : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap G) where
  h := family F G η
  h₀ := family_source F G η
  h₁ := family_target F G η
  rel := by ext n ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 元の豊穣自然変換の成分の通常の射。 -/
def componentHom (X : C) : F.obj X ⟶ G.obj X :=
  (SimplicialCategory.homEquiv' _ _).symm
    ((η.app X).app (Opposite.op ⦋0⦌) PUnit.unit)

/-- 移送した自然変換の指定頂点での辺は、元の成分の coherent な辺に一致する。 -/
lemma homotopy_component (X : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (homotopy F G η) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (componentHom F G η X)).edge := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowDataEquiv D).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow]
  change (⟨F.obj X, G.obj X, (SimplicialCategory.homEquiv' _ _).symm
    ((eComp SSet (F.obj X) (G.obj X) (G.obj X)).app (Opposite.op ⦋0⦌)
      ((η.app X).app (Opposite.op ⦋0⦌) PUnit.unit,
        (G.map X X).app (Opposite.op ⦋0⦌)
          ((eId SSet X).app (Opposite.op ⦋0⦌) PUnit.unit)))⟩ :
    Σ A B : D, A ⟶ B) = _
  have hg := ConcreteCategory.congr_hom
    (NatTrans.congr_app (G.map_id X) (Opposite.op ⦋0⦌)) PUnit.unit
  change (G.map X X).app (Opposite.op ⦋0⦌)
      ((eId SSet X).app (Opposite.op ⦋0⦌) PUnit.unit) =
    (eId SSet (G.obj X)).app (Opposite.op ⦋0⦌) PUnit.unit at hg
  rw [hg, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderCategory.base_comp_id_app]
  rfl

/-- 成分が可逆な厳密な単体的自然変換は、元の二つの ∞ 関手の同型を与える。 -/
def functorIso [Quasicategory (SimplicialNerve D)]
    (hη : ∀ X, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (componentHom F G η X)).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap G) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (homotopy F G η) (by
    intro k
    obtain ⟨X, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv C).surjective k
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (homotopy_component F G η X)).mpr (hη X))

end SerrePositivity.KST.Spectra.StrictEnrichedTransformation
