module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotBKNativeSections
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ClassifiedSectionsTriangle

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元のBE TotのBK切断比較を、同じ指定分類変換を使う共通の復元で追跡する。
方針：元の切断同型を消去し、同じR03bの全切断の余単位三角形を前合成する。
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
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotNativeSectionsRecoveryModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance strictBETotNativeSectionsRecoveryFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
local instance strictBETotNativeSectionsRecoveryCof (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsCofibrant (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y) := _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe_cofibrant A Y
local instance strictBETotNativeSectionsRecoveryKan (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    KanComplex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget).obj i) := by
  change KanComplex (exInfinity.obj _)
  infer_instance
attribute [local instance] simplicialSections_kanComplex bousfieldKanHolim_kanComplex

/-- 元の全BK切断比較は、同じ指定分類変換による復元射を回収する。 -/
def strictBETotBKNativeSections_reconstruction
    (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    let H := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
    let p := weightedNerveProjection H
    let q := coherentConeProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseSourceDiagram A K F)
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
    let η := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotBKNativeClassificationIso A K F Y
    FunctorIso
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotBKNativeSectionsEquivalence A K F Y).hom ≫
        (coherentConeSectionsIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseSourceDiagram A K F)
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))).inv) ≫
            simplicialSectionsMap (leftStraighteningInfinityReconstruction q)
              (leftStraighteningInfinityReconstruction_projection q))
      ((bousfieldKanSectionsIso H).hom ≫
        simplicialSectionsMap (classifiedFibrationTransport p q η)
          (classifiedFibrationTransport_projection p q η)) := by
  let H := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
  let p := weightedNerveProjection H
  let q := coherentConeProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseSourceDiagram A K F)
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
  let η := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotBKNativeClassificationIso A K F Y
  let E := bousfieldKanSectionsIso H
  let C := coherentConeSectionsIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseSourceDiagram A K F)
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
  change FunctorIso
    (((E.hom ≫ ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫ C.hom)) ≫ C.inv) ≫
      simplicialSectionsMap (leftStraighteningInfinityReconstruction q)
        (leftStraighteningInfinityReconstruction_projection q)) _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact FunctorIso.precomp (classifiedLeftFibrationSectionsEquivalence_triangle p q η) E.hom

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
