module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotUniverseNativeCone
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanNativeFiberPoint
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanUniverseCoefficientPoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFiber
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ClassifiedFibrationFiberComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionFiberEvaluation

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元のBK係数と同じnative錐のfiberを、元の全切断比較と両立する同値で結ぶ。
方針：同じR03cに元のfiber同型を合成し、同じ普遍BK点で評価する。
規約：IS-W2 R02〜R03の既存の合成・余単位則。全高次単体の比較を保持する。
使われ方：同じ指定BK点と標準脚の評価の、元の分類変換との照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotNativeFiberComparisonModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance strictBETotNativeFiberComparisonFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
local instance strictBETotNativeFiberComparisonCof (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsCofibrant (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y) := _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe_cofibrant A Y
local instance strictBETotNativeFiberComparisonKan (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    KanComplex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget).obj i) := by
  change KanComplex (exInfinity.obj _)
  infer_instance
attribute [local instance] simplicialSections_kanComplex bousfieldKanHolim_kanComplex
  vertexFiber_kanComplex_of_leftFibration

/-- 元のBK係数と、同じ元の図式・頂点のnative錐のfiberとの同値。 -/
def strictBETotNativeFiberEquivalence (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    QCatEquivalence ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget).obj i)
      (vertexFiber (coherentConeProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseSourceDiagram A K F)
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))) (nerveVertex i)) :=
  (qCatEquivalenceOfIso (weightedNerveFiberIso
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget) i)).trans
      (classifiedFibrationFiberEquivalence _ _ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotBKNativeClassificationIso A K F Y)
        (nerveVertex i))

/-- 同じ元の全BK切断比較は、元の係数からnative錐のfiberへの同じ同値と両立。 -/
def strictBETotNativeFiberEquivalence_sectionsIso (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    let H := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
    FunctorIso
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotBKNativeSectionsEquivalence A K F Y).hom ≫
        (coherentConeSectionsIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseSourceDiagram A K F)
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))).inv ≫
            simplicialSectionsFiberEvaluation _ (nerveVertex i))
      ((bousfieldKanSectionsIso H).hom ≫
        simplicialSectionsFiberEvaluation (weightedNerveProjection H) (nerveVertex i) ≫
          (weightedNerveFiberIso H i).inv ≫ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeFiberEquivalence A K F Y i).hom) := by
  let H := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
  let p := weightedNerveProjection H
  let q := coherentConeProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseSourceDiagram A K F)
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
  let η := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotBKNativeClassificationIso A K F Y
  let E := bousfieldKanSectionsIso H
  let C := coherentConeSectionsIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseSourceDiagram A K F)
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
  let D := weightedNerveFiberIso H i
  change FunctorIso
    ((E.hom ≫ ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫ C.hom)) ≫
      C.inv ≫ simplicialSectionsFiberEvaluation q (nerveVertex i))
    (E.hom ≫ simplicialSectionsFiberEvaluation p (nerveVertex i) ≫
      D.inv ≫ (D.hom ≫ (classifiedFibrationFiberEquivalence p q η (nerveVertex i)).hom))
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  exact FunctorIso.precomp (classifiedFibrationFiberEquivalence_sectionsIso p q η (nerveVertex i)) E.hom

/-- 同じ普遍BK点の像を、元のnative錐の同じfiberで回収する。 -/
def strictBETotNativeFiberEquivalence_universalPointIso
    (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    VertexIso
      ((simplicialSectionsFiberEvaluation _ (nerveVertex i)).app (Opposite.op ⦋0⦌)
        (((coherentConeSectionsIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseSourceDiagram A K F)
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌)
            (nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)))).inv.app (Opposite.op ⦋0⦌))
              (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseNativeConePoint A K F)))
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeFiberEquivalence A K F ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F) i).hom.app
        (Opposite.op ⦋0⦌)) (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKExInfinityCone A K F).app i).app
          (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i))))) := by
  let Y := (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F
  let H := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
  let s := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKExInfinityCone A K F
  have h := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeFiberEquivalence_sectionsIso A K F Y i).app
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint _ s)
  change VertexIso _
    (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeFiberEquivalence A K F Y i).hom.app (Opposite.op ⦋0⦌))
      (((weightedNerveFiberIso H i).inv.app (Opposite.op ⦋0⦌))
        ((simplicialSectionsFiberEvaluation (weightedNerveProjection H) (nerveVertex i)).app
          (Opposite.op ⦋0⦌) (((bousfieldKanSectionsIso H).hom.app (Opposite.op ⦋0⦌))
            (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint _ s))))) at h
  have hn := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanSectionsIso_nativeWeightedPoint_fiber _ H s i
  rw [hn] at h
  exact h

/-- 元のnative錐のfiberの指定点は、元のraw BK係数の恒等射での値の指定像に同型。 -/
def strictBETotNativeFiberEquivalence_rawPointIso
    (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (i : Kᵒᵖᵒᵖ) :
    let Y := (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F
    let j : AsSmall.{u+1} Kᵒᵖᵒᵖ := AsSmall.up.obj i
    VertexIso
      ((simplicialSectionsFiberEvaluation _ (nerveVertex j)).app (Opposite.op ⦋0⦌)
        (((coherentConeSectionsIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseSourceDiagram A K F)
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))).inv.app
            (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseNativeConePoint A K F)))
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeFiberEquivalence A K F Y j).hom.app (Opposite.op ⦋0⦌))
        ((exInfinityUnit.app ((SSet.uliftFunctor.{u+1,u}).obj
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomDiagram A K F Y).obj i))).app (Opposite.op ⦋0⦌)
            (ULift.up (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKRightHomCone A K F).app i).app
              (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i))))))) := by
  let Y := (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F
  let j : AsSmall.{u+1} Kᵒᵖᵒᵖ := AsSmall.up.obj i
  have h := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeFiberEquivalence_universalPointIso A K F j
  have hn := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanUniverseExInfinityCone_identityVertex.{u,u+1}
    Kᵒᵖᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKRightHomCone A K F) i
  change VertexIso _ (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeFiberEquivalence A K F Y j).hom.app
    (Opposite.op ⦋0⦌))
      (((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanUniverseCone.{u,u+1} Kᵒᵖᵒᵖ
          (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKRightHomCone A K F) ≫
        _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanExInfinityCoefficientUnit _ _).app (AsSmall.up.obj i)).app
          (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 j))))) at h
  rw [hn] at h
  exact h

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
