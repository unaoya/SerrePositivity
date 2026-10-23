module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackNativeEnrichmentLaws
public import SerrePositivity.InfinityCategories.F1.Cocartesian.FibrationInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.CoreEnrichedFunctor
public import SerrePositivity.InfinityCategories.F1.Coherent.NervePostcomposition
public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseHomCartesianEdges

/-!
概要：元の cocartesian fibrations の ∞ 圏の間の、実際の底変換関手。
方針：同じ全相対 Hom の制限を豊穣関手に束ね、core と coherent nerve へ移す。
規約：元の各底変換の全空間・全相対 Hom を保持する。
使われ方：分類主写像の底のセルへの制限と元の Hom 比較の降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の cocartesian fibration を、底を第一因子とする同じ pullback へ移す。 -/
def cocartesianFibrationBaseChangeObject {B D : SSet.{u}}
    (k : D ⟶ B) (p : CocartesianFibrationObject B) : CocartesianFibrationObject D :=
  ⟨Over.mk (pullback.fst k p.val.hom), kanCocartesianFibration_pullback_fst p.val.hom k⟩

/-- 同じ全相対 Hom の底変換は、元の cocartesian fibrations の間の豊穣関手。 -/
def cocartesianFibrationBaseChangeEnriched {B D : SSet.{u}} [Quasicategory B] (k : D ⟶ B) :
    EnrichedFunctor SSet.{u} (CocartesianFibrationObject B) (CocartesianFibrationObject D) where
  obj := cocartesianFibrationBaseChangeObject k
  map p q := cocartesianPullbackNativeRestriction p.val.hom q.val.hom (Over.mk k)
  map_id p := cocartesianPullbackNativeRestriction_identity p.val.hom (Over.mk k)
  map_comp p q r := cocartesianPullbackNativeRestriction_composition
    p.val.hom q.val.hom r.val.hom (Over.mk k)

/-- 同じ元の相対 Hom の core を取った底変換の豊穣関手。 -/
def cocartesianFibrationBaseChangeCoreEnriched {B D : SSet.{u}} [Quasicategory B] (k : D ⟶ B) :
    EnrichedFunctor SSet.{u} (CocartesianFibrationCategory B) (CocartesianFibrationCategory D) :=
  quasicategoryCoreEnrichedFunctor (cocartesianFibrationBaseChangeEnriched k)

/-- 元の cocartesian fibrations と全高次の可逆な相対変換に作用する底変換の ∞ 関手。 -/
def cocartesianFibrationInfinityBaseChange {B D : SSet.{u}} [Quasicategory B] (k : D ⟶ B) :
    CocartesianFibrationInfinity B ⟶ CocartesianFibrationInfinity D :=
  coherentNerveMap (cocartesianFibrationBaseChangeCoreEnriched k)

/-- 同じ底変換の ∞ 関手の頂点は、構成済みの元の pullback 対象の頂点。 -/
lemma cocartesianFibrationInfinityBaseChange_vertex {B D : SSet.{u}} [Quasicategory B]
    (k : D ⟶ B) (p : CocartesianFibrationCategory B) :
    (cocartesianFibrationInfinityBaseChange k).app (Opposite.op ⦋0⦌) (coherentNerveVertex p) =
      coherentNerveVertex ((cocartesianFibrationBaseChangeCoreEnriched k).obj p) :=
  coherentNerveMap_vertex (cocartesianFibrationBaseChangeCoreEnriched k) p

/-- この同じ底変換の Hom 作用は、元の Hom の core への実際の制限そのもの。 -/
lemma cocartesianFibrationBaseChangeCoreEnriched_map
    {B D : SSet.{u}} [Quasicategory B] (k : D ⟶ B) (p q : CocartesianFibrationCategory B) :
    (cocartesianFibrationBaseChangeCoreEnriched k).map p q =
      quasicategoryCoreMap (cocartesianPullbackNativeRestriction p.val.hom q.val.hom
        (Over.mk k)) := rfl

end SerrePositivity.InfinityCategories
