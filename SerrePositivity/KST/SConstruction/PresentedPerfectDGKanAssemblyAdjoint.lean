module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyUnit
public import SerrePositivity.KST.SConstruction.AssemblyKanModelTransport
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionKanFunctor

/-! # 同じ Ex∞ 右脚の随伴の全基点 π 同型
概要：元の厳密 dg 隣接段の右脚の随伴は、同じ Ex∞ Kan 値で全基点 π 同型。
方針：元の単位上の組み立ての厳密回収を随伴で移し、任意の Kan 模型への移送を使う。
規約：SOA の豊穣性は使わない。使われ方：実再帰 BF 列の正の Ω 条件。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の同じ隣接段の標的は、同じ Ex∞ による Kan 複体。 -/
instance presentedPerfectDGKanAssemblyTarget_kanComplex (r : ℕ) (C : PerfDGInput.{u, v} A) :
    KanComplex (((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj).right :=
  presentedPerfectDGKanAssemblyTargetFunctor_kan A r C

/-- 同じ元の右脚の随伴を、同じ元の Ex∞ Kan 対象上に保持する。 -/
def presentedPerfectDGKanAssemblyRightAdjoint (r : ℕ) (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGOneDirectionKanEnrichedFunctor A r).obj C).obj ⟶
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj :=
  (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _)
    (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyRightMap A r C)

/-- 同じ随伴は、元の単位上で元の組み立て随伴を厳密に回収する。 -/
lemma presentedPerfectDGKanAssemblyRightAdjoint_unit (r : ℕ) (C : PerfDGInput.{u, v} A) :
    exInfinityPointedUnit ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C) ≫
        presentedPerfectDGKanAssemblyRightAdjoint A r C =
      (oneDirectionAssemblyAdjointNat r).app
          (stableCategoryModel (presentedPerfectDGStableCategory A C)) ≫
        (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map
          (exInfinityPointedUnit
            ((presentedPerfectDGBoundaryPointedEnrichedFunctor A (r + 1)).obj C)) := by
  let adj := PointedSimplicialSet.smashHomAdjunction
    PointedSimplicialSet.circle.{max (u + 1) v}
  let i := exInfinityPointedUnit
    ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C)
  let j := exInfinityPointedUnit
    ((presentedPerfectDGBoundaryPointedEnrichedFunctor A (r + 1)).obj C)
  let f : ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj :=
    presentedPerfectDGKanAssemblyRightMap A r C
  let a : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C).obj) ⟶
      ((presentedPerfectDGBoundaryPointedEnrichedFunctor A (r + 1)).obj C).obj :=
    presentedPerfectDGAssemblyMap A r C
  have h := congrArg (adj.homEquiv _ _)
    (presentedPerfectDGKanAssemblyRightMap_unit A r C)
  have hl := adj.homEquiv_naturality_left i f
  have hr := adj.homEquiv_naturality_right a j
  exact hl.symm.trans (h.trans hr)

/-- 同じ元の Ex∞ 右脚の随伴は全基点・全次数で π 同型。 -/
lemma presentedPerfectDGKanAssemblyRightAdjoint_piIsomorphism (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (presentedPerfectDGKanAssemblyRightAdjoint A r C).right :=
  assemblyAdjoint_piIsomorphism_of_anodyne_units r
    (stableCategoryModel (presentedPerfectDGStableCategory A C))
    (exInfinityPointedUnit ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C))
    (exInfinityPointedUnit_anodyne _)
    (exInfinityPointedUnit ((presentedPerfectDGBoundaryPointedEnrichedFunctor A (r + 1)).obj C))
    (exInfinityPointedUnit_anodyne _) (presentedPerfectDGKanAssemblyRightAdjoint A r C)
    (presentedPerfectDGKanAssemblyRightAdjoint_unit A r C)

end SerrePositivity.KST.SConstruction
