module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.StrictTransportBaseChangeEvaluation

/-!
概要：実際の strict transport の底変換比較は、各対象で quasicategory の同値。
方針：under の制限の両端を同じ始点 fiber で評価し、既存の評価同値を消去する。
規約：構成済みの同じ比較成分の同値性を示す。
使われ方：底のセルへの制限と元の分類主写像との coherent な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
  (p : E ⟶ nerve C) [CocartesianFibration p] (k : D ⥤ C) (d : D)

/-- under の制限後の始点評価は、頂点の表示の輸送を含めて同値。 -/
lemma cocartesianStrictTransportRestrictedEvaluate_isQCatEquivalence :
    IsQCatEquivalence (cocartesianStrictTransportRestrictedEvaluate p k d) := by
  let a := nerveMap (Under.forget d) ≫ nerveMap k
  let v := nerveVertex (Under.mk (𝟙 d))
  letI : Quasicategory (vertexFiber p (a.app (Opposite.op ⦋0⦌) v)) :=
    vertexFiber_quasicategory_of_innerFibration p _
  letI : Quasicategory (vertexFiber p (nerveVertex (k.obj d))) :=
    vertexFiber_quasicategory_of_innerFibration p _
  haveI : TrivialKanFibration (kanCocartesianSectionsEvaluate p a v) :=
    kanCocartesianSectionsEvaluate_trivialKanFibration_of_fixedPrism p a v
      (exists_kanNerveInitialPrism (Under.mkIdInitial (X := d)))
  exact (isQCatEquivalence_of_trivialKanFibration (kanCocartesianSectionsEvaluate p a v)).comp
    (qCatEquivalenceOfIso (eqToIso (congrArg (vertexFiber p)
      (cocartesianStrictTransportRestricted_vertex k d)))).isQCatEquivalence

/-- 元の strict transport の under の関手による実際の制限は同値。 -/
lemma cocartesianStrictTransportUnderPost_isQCatEquivalence :
    IsQCatEquivalence (kanCocartesianSectionsPre p (cocartesianStrictTransportUnderPost k d)) := by
  letI : Quasicategory (vertexFiber p (nerveVertex (k.obj d))) :=
    vertexFiber_quasicategory_of_innerFibration p _
  apply (cocartesianStrictTransportRestrictedEvaluate_isQCatEquivalence p k d).cancel_right
  rw [cocartesianStrictTransportUnderPost_evaluate]
  exact kanCocartesianStrictTransportEvaluate_isQCatEquivalence p (k.obj d)

/-- 各底変換の元の strict transport への同じ比較成分は同値。 -/
lemma cocartesianStrictTransportBaseChangeComponent_isQCatEquivalence :
    IsQCatEquivalence (cocartesianStrictTransportBaseChangeComponent p k d) := by
  letI : InnerFibration (pullback.fst (nerveMap k) p) :=
    ⟨innerFibrations.pullback_fst _ _ (InnerFibration.mem (q := p))⟩
  exact (cocartesianStrictTransportUnderPost_isQCatEquivalence p k d).comp
    (qCatEquivalenceOfIso (cocartesianSectionsPullbackIso
      (IsPullback.of_hasPullback (nerveMap k) p).flip (nerveMap (Under.forget d))
      (nerveMap (Under.forget d) ≫ nerveMap k) rfl).symm).isQCatEquivalence

end SerrePositivity.InfinityCategories
