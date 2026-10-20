module

public import SerrePositivity.InfinityCategories.F1.StrictDiagramMappingEvaluation
public import SerrePositivity.InfinityCategories.F1.WeightedNerveEnriched

/-!
概要：simplicial replacement の全変換空間への豊穣的な作用。
方針：構成済みのパラメーター付き評価を相対 curry し、単位・合成を全次数で検査する。
規約：replacement の射影が left fibration とは主張しない。
使われ方：復元 span の両脚の高次の自然性を同じ射で記述する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- replacement は strict な変換の全空間から相対 Hom への実際の射を持つ。 -/
def simplicialReplacementMappingSpaceMap {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    strictDiagramMappingSpace F G ⟶
      relativeFunctorSpace
        (simplicialReplacementProjection G) (simplicialReplacementProjection F) :=
  relativeFunctorCurry (strictDiagramMappingReplacementEvaluation F G)
    (strictDiagramMappingReplacementEvaluation_projection F G)

/-- 同じ射の相対展開は元の全変換の評価そのもの。 -/
lemma simplicialReplacementMappingSpaceMap_uncurry {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    relativeFunctorUncurry (simplicialReplacementMappingSpaceMap F G) =
      strictDiagramMappingReplacementEvaluation F G :=
  relativeFunctorUncurry_curry _ _

/-- replacement の全変換への作用は豊穣単位を保つ。 -/
lemma simplicialReplacementMappingSpaceMap_identity {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) :
    strictDiagramMappingIdentity F ≫ simplicialReplacementMappingSpaceMap F F =
      relativeFunctorIdentity (Over.mk (simplicialReplacementProjection F)) := by
  apply relativeFunctorUncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- replacement の全変換への作用は豊穣合成を保つ。 -/
lemma simplicialReplacementMappingSpaceMap_composition {C : Type u} [Category.{u} C]
    (F G H : C ⥤ SSet.{u}) :
    strictDiagramMappingComposition F G H ≫ simplicialReplacementMappingSpaceMap F H =
      (simplicialReplacementMappingSpaceMap F G ⊗ₘ simplicialReplacementMappingSpaceMap G H) ≫
        relativeFunctorComposition
          (Over.mk (simplicialReplacementProjection F))
          (Over.mk (simplicialReplacementProjection G))
          (Over.mk (simplicialReplacementProjection H)) := by
  apply relativeFunctorUncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, η, θ⟩
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories
