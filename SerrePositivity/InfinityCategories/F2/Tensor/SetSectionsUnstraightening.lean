module

public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalPrecompositionTriangle
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.UnstraighteningTriangleComposition
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedHomInterval
public import SerrePositivity.InfinityCategories.F1.Coherent.HomIntervalVertices
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.PinchedComposition

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
namespace SerrePositivity.InfinityCategories
open HomotopyLimits
namespace SetWeight

/-- 全豊穣 Hom の区間比較を通常の射で評価すると、その同じ射の実現を得る。 -/
lemma kanEnrichedDiagramHomInterval_ordinary
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I)
    {X Y : C} (f : X ⟶ Y) :
    (kanEnrichedDiagramHomInterval D X Y rfl rfl).app (Opposite.op ⦋0⦌)
        (ULift.up (SimplicialCategory.homEquiv' X Y f)) =
      intervalMappingVertexOfEdge (((coherentNerveEdge f).map D.realization).ofEq
        (D.realization_vertex X) (D.realization_vertex Y)) := by
  change (intervalMappingPostOfEq D.realization _ _ _ _).app _
    ((coherentHomIntervalComparison X Y).app _
      (ULift.up (SimplicialCategory.homEquiv' X Y f))) = _
  rw [coherentHomIntervalComparison_vertex, Equiv.symm_apply_apply,
    intervalMappingPostOfEq_vertex]

/-- 底上の射を、相対写像空間の前合成へ写す全パラメータの作用。 -/
def relativePreHom {B : SSet.{u}} (a b c : Over B) :
    relativeFunctorSpace b.hom a.hom ⟶
      (ihom (relativeFunctorSpace c.hom b.hom)).obj
        (relativeFunctorSpace c.hom a.hom) :=
  curry ((β_ (relativeFunctorSpace c.hom b.hom)
    (relativeFunctorSpace b.hom a.hom)).hom ≫ relativeFunctorComposition a b c)

/-- 全パラメータの前合成は、指定した底上の射で元の前合成を回収する。 -/
lemma relativePreHom_vertex {B : SSet.{u}} (a b c : Over B) (f : a ⟶ b) :
    (relativePreHom a b c).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex b.hom a.hom f.left f.w) =
      functorVertex (relativeFunctorOverPre c.hom f) := by
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
    (h : VertexIso (relativeFunctorVertex b.hom a.hom f.left f.w)
      (relativeFunctorVertex b.hom a.hom g.left g.w)) :
    FunctorIso (relativeFunctorOverPre c.hom f) (relativeFunctorOverPre c.hom g) := by
  have e := h.map (relativePreHom a b c)
  simpa only [relativePreHom_vertex] using e

/-- 関手の三角形の族の評価は、三角形の面への制限と厳密に可換。 -/
lemma parameterizedDiagram_face {B K X : SSet.{u}}
    (H : (Δ[2] : SSet.{u}) ⊗ K ⟶ (ihom B).obj X) (i : Fin 3) :
    (stdSimplex.δ i ▷ (B ⊗ K)) ≫
      ((α_ Δ[2] B K).inv ≫ functorParameterizedPrism H) =
    (α_ Δ[1] B K).inv ≫
      functorParameterizedPrism ((stdSimplex.δ i ▷ K) ≫ H) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨t, b, k⟩
  rfl

/-- 指定辺による前合成を unstraightening へ写すと、その辺の像との相対合成になる。
射の族全体の同型であり、各変換ごとの比較には弱めていない。 -/
def unstraighteningPrecompositionIso {B : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (functorVertex F) (functorVertex G)) :
    FunctorIso
      (intervalPrecompose (functorVertex J)
          (Truncated.HomotopyCategory.homMk e.toTruncated) ≫
        leftUnstraighteningMappingSpaceMap F J)
      (lift
        (SSet.const (intervalMappingVertexOfEdge e) ≫
          leftUnstraighteningMappingSpaceMap F G)
        (leftUnstraighteningMappingSpaceMap G J) ≫
        relativeFunctorComposition (Over.mk (leftUnstraighteningProjection F))
          (Over.mk (leftUnstraighteningProjection G))
          (Over.mk (leftUnstraighteningProjection J))) := by
  obtain ⟨H, h₀₁, h₁₂, h₀₂⟩ :=
    intervalPrecompose_triangleFamily_exists e (functorVertex J)
  let K := leftUnstraighteningTransformationSpace G J
  let W : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u} :=
    (α_ Δ[2] B K).inv ≫ functorParameterizedPrism H
  have hw₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ W =
      coherentTransformationFamilyDiagram
        (SSet.const (intervalMappingVertexOfEdge e) : K ⟶ _) := by
    rw [W, parameterizedDiagram_face, h₀₁]
    rfl
  have hw₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ W =
      coherentTransformationFamilyDiagram (𝟙 K) := by
    rw [W, parameterizedDiagram_face, h₁₂]
    rfl
  have hw₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ W =
      coherentTransformationFamilyDiagram
        (intervalPrecompose (functorVertex J)
          (Truncated.HomotopyCategory.homMk e.toTruncated)) := by
    rw [W, parameterizedDiagram_face, h₀₂]
    rfl
  simpa only [Category.id_comp] using F2.unstraighteningMappingTriangleIso F G J
    (SSet.const (intervalMappingVertexOfEdge e)) (𝟙 K)
    (intervalPrecompose (functorVertex J)
      (Truncated.HomotopyCategory.homMk e.toTruncated)) W hw₀₁ hw₁₂ hw₀₂

/-- 同じ比較を G8 が使う pinched 写像空間へ戻す。前合成の選択も保持する。 -/
def unstraighteningPinchedPrecompositionIso {B : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (functorVertex F) (functorVertex G)) :
    FunctorIso
      (PinchedInterval.precompose (functorVertex J)
          (Truncated.HomotopyCategory.homMk e.toTruncated) ≫
        leftUnstraighteningPinchedMappingSpaceMap F J)
      (pinchedHomToIntervalMappingSpace (functorVertex G) (functorVertex J) ≫
        lift
          (SSet.const (intervalMappingVertexOfEdge e) ≫
            leftUnstraighteningMappingSpaceMap F G)
          (leftUnstraighteningMappingSpaceMap G J) ≫
          relativeFunctorComposition (Over.mk (leftUnstraighteningProjection F))
            (Over.mk (leftUnstraighteningProjection G))
            (Over.mk (leftUnstraighteningProjection J))) := by
  have h := (PinchedInterval.liftMapComparisonIso
    (intervalPrecompose (functorVertex J)
      (Truncated.HomotopyCategory.homMk e.toTruncated))).postcomp
        (leftUnstraighteningMappingSpaceMap F J)
  have k := (unstraighteningPrecompositionIso F G J e).precomp
    (pinchedHomToIntervalMappingSpace (functorVertex G) (functorVertex J))
  simpa only [leftUnstraighteningPinchedMappingSpaceMap, PinchedInterval.precompose,
    Category.assoc] using h ≪≫ k

end SetWeight
end SerrePositivity.InfinityCategories
