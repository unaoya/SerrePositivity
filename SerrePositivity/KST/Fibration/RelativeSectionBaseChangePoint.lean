module
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDoubleEvaluation
public import SerrePositivity.InfinityCategories.F1.Diagrams.RelativeSectionBaseChangeComparison

/-! # 同じ切断の底変換実現同型は、元の pullback 切断の指定点を保つ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} {J : Type u} [Category.{u} J]
  (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D)

/-- 元の底変換実現同型は、同じ豊穣切断比較の実現の端点表示だけを変えたもの。 -/
theorem relativeSectionBaseChangeRealizationIso_heq :
    HEq (relativeSectionBaseChangeRealizationIso k A)
      ((relativeSectionBaseChangeComparison k A).realizationIso
        (relativeSectionBaseChangeComparison_isQCatEquivalence k A)) := by
  unfold relativeSectionBaseChangeRealizationIso
  dsimp only [_root_.id]
  have hcast {α β : Sort (u + 2)} (h : α = β) (x : α) : HEq (Eq.mp h x) x := by
    cases h
    rfl
  exact hcast _ _

/-- 元の切断比較の指定成分を、同じ二つの標準 Kan 値で表示する。 -/
def relativeSectionBaseChangeComponentIso (X : LeftFibrationObject B) (j : J) :
    VertexIso
      (spaceInfinityVertex
        ((((relativeSectionEnrichedDiagram A).precompose
          (leftFibrationBaseChangeEnriched k)).obj j).obj X))
      (spaceInfinityVertex (((relativeSectionEnrichedDiagram (A ⋙ Over.map k)).obj j).obj X)) :=
  kanEnrichedRealizationComponentIso (relativeSectionBaseChangeComparison k A)
    (relativeSectionBaseChangeComparison_isQCatEquivalence k A) X j

/-- 同じ成分は、元の大域底変換同型の二重評価による像と HEq。 -/
theorem relativeSectionBaseChangeComponentIso_heq_doubleMap
    (X : LeftFibrationObject B) (j : J) :
    HEq (relativeSectionBaseChangeComponentIso k A X j)
      (VertexIso.map (relativeSectionBaseChangeRealizationIso k A)
        (kanEnrichedDoubleEvaluation X j)) := by
  have h := kanEnrichedRealizationComponentIso_heq_doubleMap
    (relativeSectionBaseChangeComparison k A)
    (relativeSectionBaseChangeComparison_isQCatEquivalence k A) X j
  have hm := F2.vertexIso_map_heq_of_heq (relativeSectionBaseChangeRealizationIso k A)
    ((relativeSectionBaseChangeComparison k A).realizationIso
      (relativeSectionBaseChangeComparison_isQCatEquivalence k A))
    (congrArg functorVertex ((relativeSectionEnrichedDiagram A).realization_precompose
      (leftFibrationBaseChangeEnriched k)).symm) rfl
    (relativeSectionBaseChangeRealizationIso_heq k A) (kanEnrichedDoubleEvaluation X j)
  exact h.trans hm.symm

/-- 元の同じ大域底変換同型を二重評価し、標準 Kan 値で表示した同型そのもの。 -/
theorem relativeSectionBaseChangeComponentIso_eq_doubleMap
    (X : LeftFibrationObject B) (j : J) :
    relativeSectionBaseChangeComponentIso k A X j =
      F2.isoNormalizeEndpoints
        (VertexIso.map (relativeSectionBaseChangeRealizationIso k A)
          (kanEnrichedDoubleEvaluation X j))
        (congrArg HomotopyCategory.mk
          (kanEnrichedDoubleEvaluation_precomp_vertex (relativeSectionEnrichedDiagram A)
            (leftFibrationBaseChangeEnriched k) X j))
        (congrArg HomotopyCategory.mk
          (kanEnrichedDoubleEvaluation_vertex
            (relativeSectionEnrichedDiagram (A ⋙ Over.map k)) X j)) := by
  exact (F2.isoNormalizeEndpoints_eq_of_heq _ _ _ _
    (relativeSectionBaseChangeComponentIso_heq_doubleMap k A X j).symm).symm

/-- 同じ指定成分は、元の pullback 切断の点を第一射影による同じ像へ送る。 -/
theorem relativeSectionBaseChangeComponentIso_pointHom
    (X : LeftFibrationObject B) (j : J)
    (v : ((((relativeSectionEnrichedDiagram A).precompose
      (leftFibrationBaseChangeEnriched k)).obj j).obj X).obj _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      ((((relativeSectionEnrichedDiagram A).precompose
        (leftFibrationBaseChangeEnriched k)).obj j).obj X)).symm v) ≫
      (relativeSectionBaseChangeComponentIso k A X j).hom =
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (A ⋙ Over.map k)).obj j).obj X)).symm
        ((relativeFunctorBaseChangeForward X.val.hom k (A.obj (Opposite.op j)).hom).app
          (Opposite.op ⦋0⦌) v)) :=
  kanEnrichedRealizationComponentIso_pointHom (relativeSectionBaseChangeComparison k A)
    (relativeSectionBaseChangeComparison_isQCatEquivalence k A) X j v

end SerrePositivity.KST.Fibration
