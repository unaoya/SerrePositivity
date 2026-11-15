module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotBKNativeSections
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ClassifiedSectionsTriangle

/-!
概要：元のBE TotのBK切断比較を、同じ指定分類変換を使う共通の復元で追跡する。
方針：元の切断同型を消去し、同じR03bの全切断の余単位三角形を前合成する。
規約：IS-W2 R02〜R03の既存の合成・余単位則。全高次単体の比較を保持する。
使われ方：同じ指定BK点と標準脚の評価の、元の分類変換との照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotNativeSectionsRecoveryModel : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotNativeSectionsRecoveryFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance strictBETotNativeSectionsRecoveryCof (Y : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A Y) := framedLimitProbe_cofibrant A Y
local instance strictBETotNativeSectionsRecoveryKan (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    KanComplex ((strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget).obj i) := by
  change KanComplex (exInfinity.obj _)
  infer_instance
attribute [local instance] simplicialSections_kanComplex bousfieldKanHolim_kanComplex

/-- 元の全BK切断比較は、同じ指定分類変換による復元射を回収する。 -/
def strictBETotBKNativeSections_reconstruction
    (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    let H := strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
    let p := weightedNerveProjection H
    let q := coherentConeProjection (strictBETotUniverseSourceDiagram A K F)
      ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
    let η := strictBETotBKNativeClassificationIso A K F Y
    FunctorIso
      (((strictBETotBKNativeSectionsEquivalence A K F Y).hom ≫
        (coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))).inv) ≫
            simplicialSectionsMap (leftStraighteningInfinityReconstruction q)
              (leftStraighteningInfinityReconstruction_projection q))
      ((bousfieldKanSectionsIso H).hom ≫
        simplicialSectionsMap (classifiedFibrationTransport p q η)
          (classifiedFibrationTransport_projection p q η)) := by
  let H := strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
  let p := weightedNerveProjection H
  let q := coherentConeProjection (strictBETotUniverseSourceDiagram A K F)
    ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
  let η := strictBETotBKNativeClassificationIso A K F Y
  let E := bousfieldKanSectionsIso H
  let C := coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
    ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
  change FunctorIso
    (((E.hom ≫ ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫ C.hom)) ≫ C.inv) ≫
      simplicialSectionsMap (leftStraighteningInfinityReconstruction q)
        (leftStraighteningInfinityReconstruction_projection q)) _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact FunctorIso.precomp (classifiedLeftFibrationSectionsEquivalence_triangle p q η) E.hom

end SerrePositivity.EInfinity.BarrattEccles
