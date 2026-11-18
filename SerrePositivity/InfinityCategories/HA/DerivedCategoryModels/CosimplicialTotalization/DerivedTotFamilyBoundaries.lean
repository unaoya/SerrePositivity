module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StrictDerivedTotCone
public import Mathlib.CategoryTheory.Functor.Currying

/-!
概要：G10の指定全錐族の二境界となる、同じTotと同じ全評価の全関手。
方針：全nerve単体の射列を評価関手へ後合成する。
規約：IS-W2 D01・D02の証明分割。辺の式だけで錐族を代用しない。
使われ方：HA 1.2.4、全図式射の像と指定全錐族の境界条件。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 全図式と全余単体次数での同じ評価のnerve。 -/
def strictCosimplicialEvaluationNerve :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⊗
      nerve (CosimplicialObject (Complex A)) ⟶ nerve (Complex A) where
  app _ := ↾fun p => (p.1.down.prod' p.2) ⋙
    evaluationUncurried SimplexCategory (Complex A)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro p
    rfl

/-- 全評価の族は、各図式の点で元のstrict図式そのものへ戻る。 -/
theorem strictCosimplicialEvaluationNerve_at (X : CosimplicialObject (Complex A)) :
    inv (fst ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) (Δ[0] : SSet.{u+1})) ≫
      (𝟙 _ ⊗ₘ SSet.yonedaEquiv.symm (nerveVertex X)) ≫
        strictCosimplicialEvaluationNerve A = strictCosimplicialComplexNerve X := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  let K := (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)
  let t := (inv (fst K (Δ[0] : SSet.{u+1}))).app n s
  have ht : t.1 = s := by
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (IsIso.inv_hom_id (fst K (Δ[0] : SSet.{u+1}))) n) s
  change (t.1.down.prod' ((SSet.yonedaEquiv.symm (nerveVertex X)).app n t.2)) ⋙
    evaluationUncurried SimplexCategory (Complex A) = s.down ⋙ X
  rw [ht]
  apply CategoryTheory.Functor.ext (fun _ => rfl)


/-- 全図式・全次数の実評価を同じ通常導来入口へ送る。 -/
def derivedTotEvaluationFamily :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⊗
      nerve (CosimplicialObject (Complex A)) ⟶ derivedInfinityCategory A :=
  strictCosimplicialEvaluationNerve A ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A

/-- 元の積Tot全関手の同じ導来像。 -/
def derivedTotVertexFamily :
    nerve (CosimplicialObject (Complex A)) ⟶ derivedInfinityCategory A :=
  nerveMap (productTotalFunctor A) ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A

/-- 図式射の頂点辺は、同じ積Tot関手の像そのもの。 -/
theorem derivedTotVertexFamily_map {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    (derivedTotVertexFamily A).app (Opposite.op ⦋1⦌) (nerve.edgeMk f).edge =
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌)
        (nerve.edgeMk ((productTotalFunctor A).map f)).edge := by
  change (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌)
    ((nerveMap (productTotalFunctor A)).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)) = _
  rw [nerveMap_app_mk₁]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
