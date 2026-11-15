module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotUniverseNativeCone
public import SerrePositivity.EInfinity.HomotopyWeight.BousfieldKanNativeFiberPoint
public import SerrePositivity.EInfinity.HomotopyWeight.BousfieldKanUniverseCoefficientPoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFiber
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ClassifiedFibrationFiberComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionFiberEvaluation

/-!
概要：元のBK係数と同じnative錐のfiberを、元の全切断比較と両立する同値で結ぶ。
方針：同じR03cに元のfiber同型を合成し、同じ普遍BK点で評価する。
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
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotNativeFiberComparisonModel : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotNativeFiberComparisonFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance strictBETotNativeFiberComparisonCof (Y : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A Y) := framedLimitProbe_cofibrant A Y
local instance strictBETotNativeFiberComparisonKan (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    KanComplex ((strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget).obj i) := by
  change KanComplex (exInfinity.obj _)
  infer_instance
attribute [local instance] simplicialSections_kanComplex bousfieldKanHolim_kanComplex
  vertexFiber_kanComplex_of_leftFibration

/-- 元のBK係数と、同じ元の図式・頂点のnative錐のfiberとの同値。 -/
def strictBETotNativeFiberEquivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    QCatEquivalence ((strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget).obj i)
      (vertexFiber (coherentConeProjection (strictBETotUniverseSourceDiagram A K F)
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))) (nerveVertex i)) :=
  (qCatEquivalenceOfIso (weightedNerveFiberIso
    (strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget) i)).trans
      (classifiedFibrationFiberEquivalence _ _ (strictBETotBKNativeClassificationIso A K F Y)
        (nerveVertex i))

/-- 同じ元の全BK切断比較は、元の係数からnative錐のfiberへの同じ同値と両立。 -/
def strictBETotNativeFiberEquivalence_sectionsIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    let H := strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
    FunctorIso
      ((strictBETotBKNativeSectionsEquivalence A K F Y).hom ≫
        (coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))).inv ≫
            simplicialSectionsFiberEvaluation _ (nerveVertex i))
      ((bousfieldKanSectionsIso H).hom ≫
        simplicialSectionsFiberEvaluation (weightedNerveProjection H) (nerveVertex i) ≫
          (weightedNerveFiberIso H i).inv ≫ (strictBETotNativeFiberEquivalence A K F Y i).hom) := by
  let H := strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
  let p := weightedNerveProjection H
  let q := coherentConeProjection (strictBETotUniverseSourceDiagram A K F)
    ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
  let η := strictBETotBKNativeClassificationIso A K F Y
  let E := bousfieldKanSectionsIso H
  let C := coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
    ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
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
    (F : K ⥤ (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    VertexIso
      ((simplicialSectionsFiberEvaluation _ (nerveVertex i)).app (Opposite.op ⦋0⦌)
        (((coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
            (nerveVertex ((framedLimitFunctor A K).obj F)))).inv.app (Opposite.op ⦋0⦌))
              (strictBETotUniverseNativeConePoint A K F)))
      (((strictBETotNativeFiberEquivalence A K F ((framedLimitFunctor A K).obj F) i).hom.app
        (Opposite.op ⦋0⦌)) (((strictBETotUniversalBKExInfinityCone A K F).app i).app
          (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i))))) := by
  let Y := (framedLimitFunctor A K).obj F
  let H := strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
  let s := strictBETotUniversalBKExInfinityCone A K F
  have h := (strictBETotNativeFiberEquivalence_sectionsIso A K F Y i).app
    (HomotopyWeight.nativeWeightedPoint _ s)
  change VertexIso _
    (((strictBETotNativeFiberEquivalence A K F Y i).hom.app (Opposite.op ⦋0⦌))
      (((weightedNerveFiberIso H i).inv.app (Opposite.op ⦋0⦌))
        ((simplicialSectionsFiberEvaluation (weightedNerveProjection H) (nerveVertex i)).app
          (Opposite.op ⦋0⦌) (((bousfieldKanSectionsIso H).hom.app (Opposite.op ⦋0⦌))
            (HomotopyWeight.nativeWeightedPoint _ s))))) at h
  have hn := HomotopyWeight.bousfieldKanSectionsIso_nativeWeightedPoint_fiber _ H s i
  rw [hn] at h
  exact h

/-- 元のnative錐のfiberの指定点は、元のraw BK係数の恒等射での値の指定像に同型。 -/
def strictBETotNativeFiberEquivalence_rawPointIso
    (F : K ⥤ (operad A).Algebra) (i : Kᵒᵖᵒᵖ) :
    let Y := (framedLimitFunctor A K).obj F
    let j : AsSmall.{u+1} Kᵒᵖᵒᵖ := AsSmall.up.obj i
    VertexIso
      ((simplicialSectionsFiberEvaluation _ (nerveVertex j)).app (Opposite.op ⦋0⦌)
        (((coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))).inv.app
            (Opposite.op ⦋0⦌)) (strictBETotUniverseNativeConePoint A K F)))
      (((strictBETotNativeFiberEquivalence A K F Y j).hom.app (Opposite.op ⦋0⦌))
        ((exInfinityUnit.app ((SSet.uliftFunctor.{u+1,u}).obj
          ((strictBETotProbeRightHomDiagram A K F Y).obj i))).app (Opposite.op ⦋0⦌)
            (ULift.up (((strictBETotUniversalBKRightHomCone A K F).app i).app
              (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i))))))) := by
  let Y := (framedLimitFunctor A K).obj F
  let j : AsSmall.{u+1} Kᵒᵖᵒᵖ := AsSmall.up.obj i
  have h := strictBETotNativeFiberEquivalence_universalPointIso A K F j
  have hn := HomotopyWeight.bousfieldKanUniverseExInfinityCone_identityVertex.{u,u+1}
    Kᵒᵖᵒᵖ (strictBETotUniversalBKRightHomCone A K F) i
  change VertexIso _ (((strictBETotNativeFiberEquivalence A K F Y j).hom.app
    (Opposite.op ⦋0⦌))
      (((HomotopyWeight.bousfieldKanUniverseCone.{u,u+1} Kᵒᵖᵒᵖ
          (strictBETotUniversalBKRightHomCone A K F) ≫
        HomotopyWeight.bousfieldKanExInfinityCoefficientUnit _ _).app (AsSmall.up.obj i)).app
          (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 j))))) at h
  rw [hn] at h
  exact h

end SerrePositivity.EInfinity.BarrattEccles
