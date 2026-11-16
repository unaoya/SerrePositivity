module
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingFunctoriality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberFunctorLaws
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceFiberElements
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofFrame

/-!
概要：元のfiberの全pairingを同じsource-frame評価の表示へ照合する。
方針：同じ添字の関手と評価を比較し、指定済みの全同型と底のpathを保持する。
規約：元のfiber・射・指定pathを変更せず、同値性はまだ主張しない。
使われ方：native fiberと元のroof比較を全関手上で照合する。
-/
open CategoryTheory
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet Limits
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open scoped Simplicial
attribute [local instance] jointFiberElementsModel jointFiberElementsFactorization

lemma strictBETotJointSourceFiberDomain_roof_eq (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P ⋙
      FrameHom.liftedSourceFrameArrowDomain (strictBETotJointSourceFrame A)
        (rightFrameReplacement (rightFrameFamily A)) =
      (strictBETotJointSourceRoofFrameDiagram A P).rightOp := by
  apply CategoryTheory.Functor.hext
  · intro s
    rfl
  · intro s t f
    apply heq_of_eq
    change ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
      (((strictBETotJointSourceFrame A).map (𝟙 (AsSmall.down.obj P).1.unop)).app t.obj.unop ≫
        ((strictBETotJointSourceFrame A).obj (AsSmall.down.obj P).1.unop).map
          (((simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P).map f).hom.2).unop)).op =
      ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
        (((strictBETotJointSourceFrame A).obj (AsSmall.down.obj P).1.unop).map f.down.hom.unop)).op
    rw [sameSimplicialElementsFiberFunctor_degree (strictBETotJointSourceCoefficients A) P f,
      (strictBETotJointSourceFrame A).map_id]
    simp only [NatTrans.id_app, Category.id_comp]
lemma strictBETotJointSourceFiberCodomain_roof_eq (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P ⋙
      FrameHom.liftedSourceFrameArrowCodomain (strictBETotJointSourceFrame A)
        (rightFrameReplacement (rightFrameFamily A)) =
      (Functor.const _).obj (modelRelativeObject (operad A).Algebra
        ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)) := by
  apply CategoryTheory.Functor.hext
  · intro s
    rfl
  · intro s t f
    apply heq_of_eq
    change (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
      ((rightFrameReplacement (rightFrameFamily A)).map (𝟙 (AsSmall.down.obj P).2)) = 𝟙 _
    rw [(rightFrameReplacement (rightFrameFamily A)).map_id, CategoryTheory.Functor.map_id]
lemma strictBETotJointSourceFiberPairing_roof_eq (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P) ≫
      strictBETotJointSourcePairing A =
    twistedPairingNerveMap (strictBETotJointSourceRoofFrameDiagram A P).rightOp
      ((Functor.const _).obj (modelRelativeObject (operad A).Algebra
        ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)))
      (fun s => (strictBETotJointSourceRoofFrameEvaluation A P).app (Opposite.op s)) (by
        intro s t f
        change (strictBETotJointSourceRoofFrameDiagram A P).map f.op ≫
          (strictBETotJointSourceRoofFrameEvaluation A P).app (Opposite.op s) ≫ 𝟙 _ = _
        calc
          _ = (strictBETotJointSourceRoofFrameDiagram A P).map f.op ≫
            (strictBETotJointSourceRoofFrameEvaluation A P).app (Opposite.op s) :=
              congrArg (fun g => (strictBETotJointSourceRoofFrameDiagram A P).map f.op ≫ g)
                (Category.comp_id _)
          _ = _ := ((strictBETotJointSourceRoofFrameEvaluation A P).naturality f.op).trans
            (Category.comp_id _)) := by
  have hp := twistedPairingNerveMap_precomp
    (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P)
    (FrameHom.liftedSourceFrameArrowDomain (strictBETotJointSourceFrame A)
      (rightFrameReplacement (rightFrameFamily A)))
    (FrameHom.liftedSourceFrameArrowCodomain (strictBETotJointSourceFrame A)
      (rightFrameReplacement (rightFrameFamily A)))
    (FrameHom.liftedSourceFrameArrowValue (strictBETotJointSourceFrame A)
      (rightFrameReplacement (rightFrameFamily A)))
    (FrameHom.liftedSourceFrameArrowValue_naturality (strictBETotJointSourceFrame A)
      (rightFrameReplacement (rightFrameFamily A)))
  refine hp.trans ?_
  refine twistedPairingNerveMap_congr (strictBETotJointSourceFiberDomain_roof_eq A P) (strictBETotJointSourceFiberCodomain_roof_eq A P)
    _ _ _ (by
      intro s t f
      change (strictBETotJointSourceRoofFrameDiagram A P).map f.op ≫
        (strictBETotJointSourceRoofFrameEvaluation A P).app (Opposite.op s) ≫ 𝟙 _ = _
      calc
        _ = (strictBETotJointSourceRoofFrameDiagram A P).map f.op ≫
          (strictBETotJointSourceRoofFrameEvaluation A P).app (Opposite.op s) :=
            congrArg (fun g => (strictBETotJointSourceRoofFrameDiagram A P).map f.op ≫ g)
              (Category.comp_id _)
        _ = _ := ((strictBETotJointSourceRoofFrameEvaluation A P).naturality f.op).trans
          (Category.comp_id _)) ?_
  intro s
  rfl
end SerrePositivity.EInfinity.BarrattEccles
end
