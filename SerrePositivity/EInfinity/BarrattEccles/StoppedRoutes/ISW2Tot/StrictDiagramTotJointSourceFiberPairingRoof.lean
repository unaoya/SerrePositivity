module
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingFunctoriality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberFunctorLaws
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceFiberElements
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceRoofFrame

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元のfiberの全pairingを同じsource-frame評価の表示へ照合する。
方針：同じ添字の関手と評価を比較し、指定済みの全同型と底のpathを保持する。
規約：元のfiber・射・指定pathを変更せず、同値性はまだ主張しない。
使われ方：native fiberと元のroof比較を全関手上で照合する。
-/
open _root_.CategoryTheory
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet _root_.CategoryTheory.Limits
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open scoped _root_.Simplicial
attribute [local instance] _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.jointFiberElementsModel _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.jointFiberElementsFactorization

lemma strictBETotJointSourceFiberDomain_roof_eq (A : Type u) [CommRing A] (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    simplicialElementsFiberFunctor (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A) P ⋙
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFrameArrowDomain (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A)
        (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)) =
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameDiagram A P).rightOp := by
  apply CategoryTheory.Functor.hext
  · intro s
    rfl
  · intro s t f
    apply heq_of_eq
    change ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).map
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A).map (𝟙 (AsSmall.down.obj P).1.unop)).app t.obj.unop ≫
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A).obj (AsSmall.down.obj P).1.unop).map
          (((simplicialElementsFiberFunctor (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A) P).map f).hom.2).unop)).op =
      ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).map
        (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A).obj (AsSmall.down.obj P).1.unop).map f.down.hom.unop)).op
    rw [sameSimplicialElementsFiberFunctor_degree (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A) P f,
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A).map_id]
    simp only [NatTrans.id_app, Category.id_comp]
lemma strictBETotJointSourceFiberCodomain_roof_eq (A : Type u) [CommRing A] (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    simplicialElementsFiberFunctor (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A) P ⋙
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFrameArrowCodomain (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A)
        (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)) =
      (Functor.const _).obj (modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra
        ((rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).obj (AsSmall.down.obj P).2)) := by
  apply CategoryTheory.Functor.hext
  · intro s
    rfl
  · intro s t f
    apply heq_of_eq
    change (AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).map
      ((rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).map (𝟙 (AsSmall.down.obj P).2)) = 𝟙 _
    rw [(rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).map_id, CategoryTheory.Functor.map_id]
lemma strictBETotJointSourceFiberPairing_roof_eq (A : Type u) [CommRing A] (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    nerveMap (simplicialElementsFiberFunctor (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A) P) ≫
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourcePairing A =
    twistedPairingNerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameDiagram A P).rightOp
      ((Functor.const _).obj (modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra
        ((rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).obj (AsSmall.down.obj P).2)))
      (fun s => (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameEvaluation A P).app (Opposite.op s)) (by
        intro s t f
        change (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameDiagram A P).map f.op ≫
          (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameEvaluation A P).app (Opposite.op s) ≫ 𝟙 _ = _
        calc
          _ = (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameDiagram A P).map f.op ≫
            (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameEvaluation A P).app (Opposite.op s) :=
              congrArg (fun g => (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameDiagram A P).map f.op ≫ g)
                (Category.comp_id _)
          _ = _ := ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameEvaluation A P).naturality f.op).trans
            (Category.comp_id _)) := by
  have hp := twistedPairingNerveMap_precomp
    (simplicialElementsFiberFunctor (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A) P)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFrameArrowDomain (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A)
      (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)))
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFrameArrowCodomain (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A)
      (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)))
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFrameArrowValue (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A)
      (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)))
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFrameArrowValue_naturality (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A)
      (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)))
  refine hp.trans ?_
  refine twistedPairingNerveMap_congr (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFiberDomain_roof_eq A P) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFiberCodomain_roof_eq A P)
    _ _ _ (by
      intro s t f
      change (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameDiagram A P).map f.op ≫
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameEvaluation A P).app (Opposite.op s) ≫ 𝟙 _ = _
      calc
        _ = (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameDiagram A P).map f.op ≫
          (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameEvaluation A P).app (Opposite.op s) :=
            congrArg (fun g => (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameDiagram A P).map f.op ≫ g)
              (Category.comp_id _)
        _ = _ := ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameEvaluation A P).naturality f.op).trans
          (Category.comp_id _)) ?_
  intro s
  rfl
end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
end
