module

public import SerrePositivity.InfinityCategories.F1.CocartesianOneBoundaryFaceInducedOriginal
public import SerrePositivity.InfinityCategories.F1.CocartesianTwoHornSharedOriginal

/-!
概要：面側の大域同型が指定する共有境界像を、二次内ホーンの全 Hom へ反映する。
方針：同じ元の大域 Hom 上の三角形を、同値なホーン制限の前合成で反映する。
規約：元の分類主写像と面側から指定した共有境界像を保持する。
使われ方：大域同型を伴う coherent な二次元境界比較の貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "τ" => stdSimplex.δ (1 : Fin 3) ≫ σ
local notation "R" => cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
  (cocartesianFiniteHornOver 2 1)
local notation "V" => cocartesianOneBoundaryHomComparison j τ p q
local notation "N" => cocartesianTwoHornSharedNativeRestriction p q
local notation "T" => cocartesianTwoHornSharedTargetRestriction p q
local notation "H" => cocartesianTwoHornNativeTargetComparison p q

local instance {D : SSet.{u}} (a : D ⟶ nerve (ULift.{u} (Fin 3))) :
    InnerFibration (pullback.fst a q.val.hom) :=
  ⟨innerFibrations.pullback_fst a q.val.hom (InnerFibration.mem (q := q.val.hom))⟩

/-- 面側が指定する共有境界の大域同型を、同じホーン経由の表示へ移す。 -/
def cocartesianTwoHornFaceInducedOriginalIso :
    FunctorIso (R ≫ (N ≫ V)) (cocartesianTwoHornSharedOriginalTargetAction p q) := by
  have h := cocartesianOneBoundaryFaceInducedOriginalIso j τ p q
  dsimp only [cocartesianOneBoundaryDiagramComparison] at h
  apply F2.functorIsoOfEq h
  · rw [← Category.assoc, cocartesianTwoHornSharedNativeRestriction_original]
    rfl
  · rfl

/-- 同じ面側の指定像から反映した、ホーンの共有境界への逆向き自然性。 -/
def cocartesianTwoHornFaceCoherenceReverseIso : FunctorIso (H ≫ T) (N ≫ V) :=
  homTransportTriangleCoherence
    (cocartesianTwoHornSharedOriginalTargetAction p q)
    (cocartesianTwoHornOriginalTargetAction p q) R T H (N ≫ V)
    (cocartesianTwoHornNativeLiftRestriction_isQCatEquivalence p q)
    (cocartesianTwoHornSharedTargetOriginalIso p q)
    (cocartesianTwoHornNativeTargetComparison_originalIso p q)
    (cocartesianTwoHornFaceInducedOriginalIso j p q)

/-- 面側と同じ共有境界像を指定した、全ホーン Hom 上の自然性。 -/
def cocartesianTwoHornFaceCoherenceIso : FunctorIso (N ≫ V) (H ≫ T) :=
  (cocartesianTwoHornFaceCoherenceReverseIso j p q).symm

/-- 同じ自然性の大域制限は、面側が指定した三角形そのものを回収する。 -/
lemma cocartesianTwoHornFaceCoherenceReverseIso_original :
    (cocartesianTwoHornFaceCoherenceReverseIso j p q).precomp R ≪≫
      cocartesianTwoHornFaceInducedOriginalIso j p q =
    (cocartesianTwoHornNativeTargetComparison_originalIso p q).postcomp T ≪≫
      cocartesianTwoHornSharedTargetOriginalIso p q :=
  homTransportTriangleCoherence_identity
    (cocartesianTwoHornSharedOriginalTargetAction p q)
    (cocartesianTwoHornOriginalTargetAction p q) R T H (N ≫ V)
    (cocartesianTwoHornNativeLiftRestriction_isQCatEquivalence p q)
    (cocartesianTwoHornSharedTargetOriginalIso p q)
    (cocartesianTwoHornNativeTargetComparison_originalIso p q)
    (cocartesianTwoHornFaceInducedOriginalIso j p q)

end SerrePositivity.InfinityCategories
