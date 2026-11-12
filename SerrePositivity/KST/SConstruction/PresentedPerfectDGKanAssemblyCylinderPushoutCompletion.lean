module
public import
  SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyCylinderPushoutNaturality
public import SerrePositivity.KST.SConstruction.ExInfinityPointedUnitWhisker

/-! # 同じ実円柱押し出しの関手的 Ex∞ Kan 値
概要：実押し出しを同じ Ex∞ へ送り、元の両標的からの実比較を保持する。
方針：厳密豊穣関手を合成し、元の比較の後に同じ単位を合成する。
規約：BF の全帰納列の完成とは数えない。使われ方：BF 帰納段の Kan 候補。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ実円柱押し出しの Ex∞ 値を持つ標準点つき厳密豊穣関手。 -/
def presentedPerfectDGKanAssemblyCylinderCompletionFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  (presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).comp SSet
    exInfinityPointedEnrichedFunctor

/-- 同じ実円柱押し出しの Ex∞ 値は、同じ全 Hom を持つ Kan 対象。 -/
def presentedPerfectDGKanAssemblyCylinderCompletionKanFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedKanObject.{max (u + 1) v} :=
  (presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).comp SSet
    exInfinityPointedKanEnrichedFunctor

/-- 同じ Kan 値は、元の実押し出しの基点を同じ単位で写した対象。 -/
lemma presentedPerfectDGKanAssemblyCylinderCompletionFunctor_obj (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C).obj =
      Under.mk ((((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app
          (((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj).right) := rfl

/-- 元の実押し出しから同じ Ex∞ 値への、元の単位成分。 -/
def presentedPerfectDGKanAssemblyCylinderCompletionUnit (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C ⟶
      (presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C :=
  exInfinityPointedUnit ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C)

/-- 同じ元の単位成分は、基礎単体集合上で anodyne。 -/
lemma presentedPerfectDGKanAssemblyCylinderCompletionUnit_anodyne (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    anodyneExtensions
      (show ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj ⟶
        ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C).obj from
          presentedPerfectDGKanAssemblyCylinderCompletionUnit A r C).right :=
  exInfinityPointedUnit_anodyne ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C)

/-- 元の左標的から Kan 値への、同じ実左比較と単位の合成。 -/
def presentedPerfectDGKanAssemblyCylinderCompletionLeftMap (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C ⟶
      (presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C :=
  presentedPerfectDGKanAssemblyCylinderPushoutLeftMap A r C ≫
    presentedPerfectDGKanAssemblyCylinderCompletionUnit A r C

/-- 元の右標的から Kan 値への、同じ実右包含と単位の合成。 -/
def presentedPerfectDGKanAssemblyCylinderCompletionRightMap (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyTargetFunctor A r).obj C ⟶
      (presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C :=
  presentedPerfectDGKanAssemblyCylinderPushoutRightMap A r C ≫
    presentedPerfectDGKanAssemblyCylinderCompletionUnit A r C

end SerrePositivity.KST.SConstruction
