module

public import SerrePositivity.InfinityCategories.F1.Weighted.NerveCocartesianFunctor
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveEnriched
public import SerrePositivity.InfinityCategories.F1.Diagrams.StrictDiagramMappingVertices
public import SerrePositivity.InfinityCategories.F1.Cocartesian.RelativeComposition

/-!
概要：weighted nerve の全パラメーターの作用を cocartesian 相対関手空間へ制限する。
方針：全ての頂点を元の自然変換で表示し、その辺の保存から全部分複体へ持ち上げる。
規約：頂点だけでなく、元の単位・合成を保つ同じ単体集合の射を使う。
使われ方：Cat∞ 値 unstraightening の豊穣関手と写像空間比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- cocartesian 関手の全部分複体の包含は単射。 -/
instance cocartesianRelativeFunctorInclusion_mono {E D B : SSet.{u}}
    (p : E ⟶ B) (q : D ⟶ B) : Mono (cocartesianRelativeFunctorInclusion p q) :=
  inferInstanceAs (Mono
    (fullSubcomplexOnVertices _ (cocartesianRelativeFunctorPredicate p q)).ι)

/-- 元の全パラメーターの作用は通常の自然変換で実際の weighted nerve の射を回収する。 -/
lemma weightedNerveMappingSpaceMap_vertex {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) :
    (weightedNerveMappingSpaceMap F G).app (Opposite.op ⦋0⦌) (strictDiagramMappingVertex η) =
      relativeFunctorVertex (weightedNerveProjection G) (weightedNerveProjection F)
        (weightedNerveMap η) (weightedNerveMap_projection η) := by
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, τ⟩
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext i
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 元の全次数の weighted nerve の作用は cocartesian 関手の全部分複体に入る。 -/
def weightedNerveCocartesianMappingSpaceMap {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] [∀ c, Quasicategory (G.obj c)] :
    strictDiagramMappingSpace F G ⟶
      cocartesianRelativeFunctorSpace (weightedNerveProjection F) (weightedNerveProjection G) :=
  fullSubcomplexLift _ (weightedNerveMappingSpaceMap F G) (by
    intro v
    obtain ⟨η, rfl⟩ := exists_strictDiagramMappingVertex F G v
    rw [weightedNerveMappingSpaceMap_vertex, cocartesianRelativeFunctorPredicate_vertex]
    exact weightedNerveMap_preservesCocartesianEdges η)

/-- 全部分複体へ制限しても、包含後には元の全パラメーターの作用となる。 -/
lemma weightedNerveCocartesianMappingSpaceMap_ι {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] [∀ c, Quasicategory (G.obj c)] :
    weightedNerveCocartesianMappingSpaceMap F G ≫
      cocartesianRelativeFunctorInclusion (weightedNerveProjection F) (weightedNerveProjection G) =
        weightedNerveMappingSpaceMap F G := rfl

/-- cocartesian 相対空間への同じ作用は元の豊穣単位を保つ。 -/
lemma weightedNerveCocartesianMappingSpaceMap_identity {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] :
    strictDiagramMappingIdentity F ≫ weightedNerveCocartesianMappingSpaceMap F F =
      cocartesianRelativeFunctorIdentity (Over.mk (weightedNerveProjection F)) := by
  apply (cancel_mono
    (cocartesianRelativeFunctorInclusion (weightedNerveProjection F) (weightedNerveProjection F))).1
  exact weightedNerveMappingSpaceMap_identity F

/-- cocartesian 相対空間への同じ作用は元の全パラメーターの豊穣合成を保つ。 -/
lemma weightedNerveCocartesianMappingSpaceMap_composition {C : Type u} [Category.{u} C]
    (F G H : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)]
    [∀ c, Quasicategory (G.obj c)] [∀ c, Quasicategory (H.obj c)] :
    strictDiagramMappingComposition F G H ≫ weightedNerveCocartesianMappingSpaceMap F H =
      (weightedNerveCocartesianMappingSpaceMap F G ⊗ₘ
        weightedNerveCocartesianMappingSpaceMap G H) ≫
        cocartesianRelativeFunctorComposition (Over.mk (weightedNerveProjection F))
          (Over.mk (weightedNerveProjection G)) (Over.mk (weightedNerveProjection H)) := by
  apply (cancel_mono
    (cocartesianRelativeFunctorInclusion (weightedNerveProjection F) (weightedNerveProjection H))).1
  exact weightedNerveMappingSpaceMap_composition F G H

end SerrePositivity.InfinityCategories
