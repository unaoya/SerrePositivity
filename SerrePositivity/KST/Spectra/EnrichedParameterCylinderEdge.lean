module

public import SerrePositivity.KST.Spectra.EnrichedOrderedCylinderBridge

/-!
概要：指定したパラメータによる二対象の円柱の辺と、nerve の pairing での計算。
方針：標準区間の順序写像を二段の円柱へ送り、比較関手を合成する。
規約：頂点ごとの同一視ではなく、単体集合の射の等式。使われ方：評価の族の外辺。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.EnrichedParameterCylinder

/-- 一点の豊穣圏への定値図式。 -/
def pointDiagram {T : Type w} [EnrichedCategory SSet.{u} T] :
    EnrichedFunctor SSet.{u} T _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{v} where
  obj _ := ⟨PUnit.unit⟩
  map _ _ := toUnit _
  map_id _ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨⟩
    rfl
  map_comp _ _ _ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro f
    rfl

variable {A : SSet.{u}} (i : 𝟙_ SSet.{u} ⟶ A)

/-- 指定した単位パラメータの、二対象の円柱内の実際の辺。 -/
def parameterEdge : (Δ[1] : SSet.{max u v}) ⟶ SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{v}) where
  app _ := ↾fun t ↦ (EnrichedOrderedCylinder.simplexPair (stdSimplex.asOrderHom t)
    pointDiagram).comp SSet (EnrichedOrderedCylinder.bridge i)
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro t
    refine EnrichedFunctor.ext SSet ?_ ?_
    · intro X
      rfl
    · intro X Y
      rfl

/-- 順序の証明と Hom の pairing は、二段の円柱の比較と厳密に可換。 -/
lemma pair_bridge {C : Type v} [EnrichedCategory SSet.{u} C]
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin 2) C) {U : SSet.{u}}
    (p : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.orderWitness (Fin 2) X.position Y.position)
    (k : U ⟶ 𝟙_ SSet.{u}) (f : U ⟶ (X.val ⟶[SSet] Y.val)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide A (EnrichedOrderedCylinder.bridgeObject X).side
        (EnrichedOrderedCylinder.bridgeObject Y).side
        (lift p k ≫ (EnrichedOrderedCylinder.bridge (C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{v}) i).map
          ⟨X.position, ⟨PUnit.unit⟩⟩ ⟨Y.position, ⟨PUnit.unit⟩⟩) f =
      lift p f ≫ (EnrichedOrderedCylinder.bridge i).map X Y := by
  rcases X with ⟨j, x⟩
  rcases Y with ⟨l, y⟩
  fin_cases j <;> fin_cases l
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 指定したパラメータの辺に沿った pairing は、二段の円柱の比較そのもの。 -/
lemma nervePair_parameterEdge :
    (𝟙 (SimplicialNerve C) ⊗ₘ parameterEdge i) ≫ nervePair A =
      EnrichedOrderedCylinder.nerveSimplexFamily 1 ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (EnrichedOrderedCylinder.bridge (C := C) i) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨F, t⟩
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairFunctor A F
      ((EnrichedOrderedCylinder.simplexPair (stdSimplex.asOrderHom t)
        pointDiagram).comp SSet (EnrichedOrderedCylinder.bridge i)) =
    (EnrichedOrderedCylinder.simplexPair (stdSimplex.asOrderHom t) F).comp SSet
      (EnrichedOrderedCylinder.bridge i)
  refine EnrichedFunctor.ext SSet ?_ ?_
  · intro X
    rfl
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide A
      ((EnrichedOrderedCylinder.bridge (C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{v}) i).obj
        ⟨(stdSimplex.asOrderHom t) X.as.down, ⟨PUnit.unit⟩⟩).side
      ((EnrichedOrderedCylinder.bridge (C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{v}) i).obj
        ⟨(stdSimplex.asOrderHom t) Y.as.down, ⟨PUnit.unit⟩⟩).side
      (lift (EnrichedOrderedCylinder.pathOrderMap (stdSimplex.asOrderHom t) X Y)
          (toUnit _) ≫ (EnrichedOrderedCylinder.bridge (C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{v}) i).map
        ⟨(stdSimplex.asOrderHom t) X.as.down, ⟨PUnit.unit⟩⟩
        ⟨(stdSimplex.asOrderHom t) Y.as.down, ⟨PUnit.unit⟩⟩) (F.map X Y) =
    lift (EnrichedOrderedCylinder.pathOrderMap (stdSimplex.asOrderHom t) X Y)
        (F.map X Y) ≫ (EnrichedOrderedCylinder.bridge (C := C) i).map
      ⟨(stdSimplex.asOrderHom t) X.as.down, F.obj X⟩
      ⟨(stdSimplex.asOrderHom t) Y.as.down, F.obj Y⟩
  exact pair_bridge (C := C) i
    ⟨(stdSimplex.asOrderHom t) X.as.down, F.obj X⟩
    ⟨(stdSimplex.asOrderHom t) Y.as.down, F.obj Y⟩
    (EnrichedOrderedCylinder.pathOrderMap (stdSimplex.asOrderHom t) X Y)
    (toUnit _) (F.map X Y)

end SerrePositivity.KST.Spectra.EnrichedParameterCylinder
