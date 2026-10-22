module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramComma
public import SerrePositivity.InfinityCategories.F2.Ind.CommaSimplexSmallness

/-!
概要：元の全図式 comma の実際の単体は小さい宇宙に属する。
方針：Space∞ の固定頂点符号化を前層・Ind・全図式へ伝え、comma に適用する。
規約：小ささを仮定しない。使われ方：実同型による小さい図式表示添字。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

local instance uliftObjectSmall (A : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj A).obj n) :=
  inferInstanceAs (Small.{u} (ULift.{u + 1} (A.obj n)))

/-- 元の Ind 圏への固定頂点の全写像は小さい。 -/
lemma ind_hasSmallFixedVertexMaps (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] :
    HasSmallFixedVertexMaps (IndInfinity κ C) := by
  haveI : Mono (indInclusionPresheaf κ C) :=
    inferInstanceAs (Mono (fullSubcomplexOnVertices (PresheafInfinity C) (IsIndVertex κ C)).ι)
  have h : HasSmallFixedVertexMaps (PresheafInfinity C) :=
    space_hasSmallFixedVertexMaps.functorSpace ((SSet.uliftFunctor.{u + 1, u}).obj C.op)
  exact HasSmallFixedVertexMaps.of_mono (indInclusionPresheaf κ C) h

/-- 元の Ind 全図式圏への固定頂点の全写像も小さい。 -/
lemma indDiagram_hasSmallFixedVertexMaps (κ : Cardinal.{u}) (K C : SSet.{u})
    [Quasicategory C] : HasSmallFixedVertexMaps
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj K)).obj (IndInfinity κ C)) :=
  (ind_hasSmallFixedVertexMaps κ C).functorSpace ((SSet.uliftFunctor.{u + 1, u}).obj K)

/-- 指定された元の全 Ind 図式への comma は各次数で小さい。 -/
instance diagramComma_obj_small (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)
    (n : SimplexCategoryᵒᵖ) : Small.{u} ((diagramComma κ D).obj n) :=
  leftKanShape_obj_small_of_fixedVertexMaps (diagramYoneda κ K C) (functorVertex D)
    (indDiagram_hasSmallFixedVertexMaps κ K C) n

end SerrePositivity.InfinityCategories.F2.Ind
