module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.IntervalPrecompositionTriangle
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.UnstraighteningTriangleComposition
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedHomInterval
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomIntervalVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedComposition

/-!
概要：篩包含の比較に使う、指定辺の前合成と unstraightening の全写像空間作用。
方針：選択済み前合成の三角形の族を評価し、指定三角形の相対合成比較へ渡す。
規約：指定辺と前合成射を変更せず、全パラメータを保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors

namespace SetWeight

/-- 全豊穣 Hom の区間比較を通常の射で評価すると、その同じ射の実現を得る。 -/
lemma kanEnrichedDiagramHomInterval_ordinary
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {I : Type u} [SmallCategory I] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C I)
    {X Y : C} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramHomInterval D X Y rfl rfl).app (Opposite.op ⦋0⦌)
        (ULift.up (SimplicialCategory.homEquiv' X Y f)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map D.realization).ofEq
        (D.realization_vertex X) (D.realization_vertex Y)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq D.realization _ _
    (D.realization_vertex X) (D.realization_vertex Y)).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y).app _
      (ULift.up (SimplicialCategory.homEquiv' X Y f))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex, Equiv.symm_apply_apply,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_vertex]

/-- 底上の射を、相対写像空間の前合成へ写す全パラメータの作用。 -/
def relativePreHom {B : SSet.{u}} (a b c : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom ⟶
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace c.hom b.hom)).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace c.hom a.hom) :=
  curry ((β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace c.hom b.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a b c)

/-- 全パラメータの前合成は、指定した底上の射で元の前合成を回収する。 -/
lemma relativePreHom_vertex {B : SSet.{u}} (a b c : Over B) (f : a ⟶ b) :
    (relativePreHom a b c).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex b.hom a.hom f.left f.w) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre c.hom f) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro m β
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 相対写像空間内の比較同型から、前合成の全写像空間上の同型を得る。 -/
def relativePreIso {B : SSet.{u}} (a b c : Over B) (f g : a ⟶ b)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex b.hom a.hom f.left f.w)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex b.hom a.hom g.left g.w)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre c.hom f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre c.hom g) := by
  have e := h.map (relativePreHom a b c)
  simpa only [relativePreHom_vertex] using e

/-- 関手の三角形の族の評価は、三角形の面への制限と厳密に可換。 -/
lemma parameterizedDiagram_face {B K X : SSet.{u}}
    (H : (Δ[2] : SSet.{u}) ⊗ K ⟶ (ihom B).obj X) (i : Fin 3) :
    (stdSimplex.δ i ▷ (B ⊗ K)) ≫
      ((α_ Δ[2] B K).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism H) =
    (α_ Δ[1] B K).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism ((stdSimplex.δ i ▷ K) ≫ H) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨t, b, k⟩
  rfl

/-- 指定辺による前合成を unstraightening へ写すと、その辺の像との相対合成になる。
射の族全体の同型であり、各変換ごとの比較には弱めていない。 -/
def unstraighteningPrecompositionIso {B : SSet.{u + 1}}
    (F G J : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (e : SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)
          (Truncated.HomotopyCategory.homMk e.toTruncated) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingSpaceMap F J)
      (lift
        (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingSpaceMap F G)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingSpaceMap G J) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition (Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F))
          (Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection G))
          (Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection J))) := by
  let h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalPrecompose_triangleFamily_exists e (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)
  let H := Classical.choose h
  have h₀₁ := (Classical.choose_spec h).1
  have h₁₂ := (Classical.choose_spec h).2.1
  have h₀₂ := (Classical.choose_spec h).2.2
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace G J
  let W : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
    (α_ Δ[2] B K).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism H
  have hw₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ W =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram
        (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e) : K ⟶ _) := by
    exact (parameterizedDiagram_face H 2).trans
      (congrArg (fun T => (α_ Δ[1] B K).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism T) h₀₁)
  have hw₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ W =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram (𝟙 K) := by
    exact (parameterizedDiagram_face H 0).trans
      (congrArg (fun T => (α_ Δ[1] B K).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism T) h₁₂)
  have hw₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ W =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)
          (Truncated.HomotopyCategory.homMk e.toTruncated)) := by
    exact (parameterizedDiagram_face H 1).trans
      (congrArg (fun T => (α_ Δ[1] B K).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism T) h₀₂)
  simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.unstraighteningMappingTriangleIso F G J
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e)) (𝟙 K)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)
      (Truncated.HomotopyCategory.homMk e.toTruncated)) W hw₀₁ hw₁₂ hw₀₂

/-- 同じ比較を G8 が使う pinched 写像空間へ戻す。前合成の選択も保持する。 -/
def unstraighteningPinchedPrecompositionIso {B : SSet.{u + 1}}
    (F G J : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (e : SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)
          (Truncated.HomotopyCategory.homMk e.toTruncated) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningPinchedMappingSpaceMap F J)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J) ≫
        lift
          (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingSpaceMap F G)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingSpaceMap G J) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition (Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F))
            (Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection G))
            (Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection J))) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.liftMapComparisonIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)
      (Truncated.HomotopyCategory.homMk e.toTruncated))).postcomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingSpaceMap F J)
  have k := (unstraighteningPrecompositionIso F G J e).precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J))
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningPinchedMappingSpaceMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose,
    Category.assoc] using h ≪≫ k

end SetWeight
end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
