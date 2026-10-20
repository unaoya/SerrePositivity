module

public import SerrePositivity.InfinityCategories.F1.QuasicategoryDiagramRealization
public import SerrePositivity.InfinityCategories.F1.QCatDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.F1.KanDiagramConstantParameter

/-!
概要：元の quasicategory 値図式を固定した実現は、その同じ通常の図式の coherent 表示。
方針：元の恒等変換の混合評価を、同じ図式の射の豊穣表示へ戻す。
規約：各対象でなく図式全体の全単体について計算する。
使われ方：底変換比較の実際の辺を元の比較成分で評価する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の図式の全対象と全ての射を、同じ QCat 値図式へ束ねる。 -/
def quasicategoryDiagramValueFunctor {C : Type u} [Category.{u} C]
    (F : QuasicategoryDiagramCategory C) : C ⥤ QCat.{u} where
  obj c := quasicategoryDiagramValue F c
  map f := F.val.map f
  map_id c := F.val.map_id c
  map_comp f g := F.val.map_comp f g

/-- 定値な元の図式パラメーターの対角評価は、その同じ通常の図式の coherent 表示。 -/
lemma diagonalQuasicategoryDiagramEvaluation_constant
    {C J : Type u} [Category.{u} C] [LinearOrder J]
    (A : J ⥤ C) (F : QuasicategoryDiagramCategory C) :
    diagonalQuasicategoryDiagramEvaluation A (enrichedConstantOrderDiagram J F) =
      enrichedFunctorOfOrderDiagram (A ⋙ quasicategoryDiagramValueFunctor F) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  have hij : i.as ≤ j.as := SimplicialThickening.Path.le (P.obj 0)
  change (diagonalQuasicategoryDiagramHom A (enrichedConstantOrderDiagram J F) i j).app n P = _
  erw [diagonalQuasicategoryDiagramHom_of_le A (enrichedConstantOrderDiagram J F) i j hij]
  apply Subtype.ext
  change ((toUnit _ ≫ strictDiagramMappingIdentity (F.val ⋙ quasicategoryObjectForget) ≫
    strictDiagramMixedHom (A.map (homOfLE hij))
      (F.val ⋙ quasicategoryObjectForget) (F.val ⋙ quasicategoryObjectForget)).app n) P =
    PinchedHom.constant (functorVertex (F.val.map (A.map (homOfLE hij)))) n.unop.len
  rw [strictDiagramMixedHom_identity]
  exact unitHom_app_constant (curry' (F.val.map (A.map (homOfLE hij)))) n.unop.len

/-- 実現の図式パラメーターを頂点に固定すると、元の図式の coherent 表示の同じ単体。 -/
lemma quasicategoryDiagramDiagonalSimplex_constant {C : Type u} [Category.{u} C]
    (F : QuasicategoryDiagramCategory C) {n : ℕ} (σ : (nerve C) _⦋n⦌) :
    quasicategoryDiagramDiagonalSimplex σ (PinchedHom.constant (coherentNerveVertex F) n) =
      (qCatDiagramCoherentNerve (quasicategoryDiagramValueFunctor F)).app (Opposite.op ⦋n⦌)
        (ULift.up σ) := by
  change diagonalQuasicategoryDiagramEvaluation (strictDiagramSimplexBase σ)
    (PinchedHom.constant (coherentNerveVertex F) n) = enrichedFunctorOfOrderDiagram _
  rw [coherentNerveVertex_constant, diagonalQuasicategoryDiagramEvaluation_constant]
  rfl

end SerrePositivity.InfinityCategories
