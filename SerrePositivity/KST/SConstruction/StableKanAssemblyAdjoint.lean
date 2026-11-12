module
public import SerrePositivity.KST.SConstruction.StableKanAssemblySpanNaturality
public import SerrePositivity.KST.SConstruction.AssemblyKanModelTransport
public import SerrePositivity.KST.SConstruction.ExInfinitySuspensionAssemblyUnit

/-!
概要：元の同じ Kan 隣接段右脚の随伴が全基点 π 同型であることを示す。
方針：同じ Ex∞ 単位上で元の組み立て随伴を回収し、既存の Kan 模型移送を使う。
規約：SOA の豊穣性を仮定しない。使われ方：有限 native BF 正段の Ω 条件。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet InfinityCategories LocalizingInvariants
open Spectra

/-- 概要：同じ元の右標的は Kan 複体。
方針：同じ境界商の Ex∞ の Kan 性を使う。
規約：追加 instance 仮定なし。使われ方：元の右随伴の Ω 条件。 -/
instance stableKanAssemblyTarget_kanComplex (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    KanComplex (((stableKanAssemblyTargetFunctor r).obj C).obj).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _

/-- 概要：同じ元の右脚を同じ実 Kan 対象間の随伴にする。
方針：元の suspension-loop 随伴を適用する。
規約：元の実右脚を保持。使われ方：有限 BF 構造随伴の比較。 -/
def stableKanAssemblyRightAdjoint (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    ((stableOneDirectionKanEnrichedFunctor r).obj C).obj ⟶
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((stableKanAssemblyTargetFunctor r).obj C).obj :=
  (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _)
    (show ((stableKanAssemblySourceFunctor r).obj C).obj ⟶
      ((stableKanAssemblyTargetFunctor r).obj C).obj from stableKanAssemblyRightMap r C)

/-- 概要：同じ右随伴は Ex∞ 単位上で元の組み立て随伴を厳密に回収する。
方針：元の suspension 単位の回収式を同じ随伴で移す。
規約：元の二単位を保持。使われ方：既存の Kan 模型移送への入力。 -/
lemma stableKanAssemblyRightAdjoint_unit (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    exInfinityPointedUnit ((stableOneDirectionPointedEnrichedFunctor r).obj C) ≫
        stableKanAssemblyRightAdjoint r C =
      (oneDirectionAssemblyAdjointNat r).app (stableCategoryModel C) ≫
        (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map
          (exInfinityPointedUnit ((stableBoundaryPointedEnrichedFunctor (r + 1)).obj C)) := by
  let adj := PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}
  let i := exInfinityPointedUnit ((stableOneDirectionPointedEnrichedFunctor r).obj C)
  let j := exInfinityPointedUnit ((stableBoundaryPointedEnrichedFunctor (r + 1)).obj C)
  let f : ((stableKanAssemblySourceFunctor r).obj C).obj ⟶
      ((stableKanAssemblyTargetFunctor r).obj C).obj := stableKanAssemblyRightMap r C
  let a : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (((stableOneDirectionPointedEnrichedFunctor r).obj C).obj) ⟶
      ((stableBoundaryPointedEnrichedFunctor (r + 1)).obj C).obj :=
    stableSuspensionAssemblyMap r C
  have h := congrArg (adj.homEquiv _ _)
    (exInfinitySuspensionAssembly_unit (stableSuspensionAssemblyMap r C))
  have hl := adj.homEquiv_naturality_left i f
  have hr := adj.homEquiv_naturality_right a j
  exact hl.symm.trans (h.trans hr)

/-- 概要：同じ元の右随伴は全基点・全次数で π 同型。
方針：元の組み立て随伴を同じ二つの anodyne 単位で Kan 模型へ移す。
規約：元の実随伴を保持。使われ方：有限 BF 正段の実 Ω 条件。 -/
lemma stableKanAssemblyRightAdjoint_piIsomorphism (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (stableKanAssemblyRightAdjoint r C).right :=
  assemblyAdjoint_piIsomorphism_of_anodyne_units r (stableCategoryModel C)
    (exInfinityPointedUnit ((stableOneDirectionPointedEnrichedFunctor r).obj C))
    (exInfinityPointedUnit_anodyne _)
    (exInfinityPointedUnit ((stableBoundaryPointedEnrichedFunctor (r + 1)).obj C))
    (exInfinityPointedUnit_anodyne _) (stableKanAssemblyRightAdjoint r C)
    (stableKanAssemblyRightAdjoint_unit r C)

end SerrePositivity.KST.SConstruction
