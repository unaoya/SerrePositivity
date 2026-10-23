module

public import SerrePositivity.InfinityCategories.F1.Transport.PointProductSquareRestriction

/-!
概要：点上の表現空間の族の比較は積射影の実際の底変換制限に自然。
方針：引き戻しの全空間の同型と四角形の自然性を表現空間へ制限する。
規約：底側と全空間側の全高次データを厳密に保つ。
使われ方：区間境界制限定理を点上の表現の区間族へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) :
    LeftFibration (pullback.snd p g) :=
  ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩

/-- 概要：積射影の実際の表現空間の底変換制限を新しい積の全空間へ戻す。
方針：実際の制限に引き戻しの全空間の同型による比較を続ける。
規約：パラメーターの充填性は不要。
使われ方：点上の表現の族の実際の境界制限。 -/
def pointProductWitnessPre (E : SSet.{u + 1}) [KanComplex E]
    {K L : SSet.{u + 1}} (i : L ⟶ K) :
    transportWitnessSpace (snd E K) ⟶ transportWitnessSpace (snd E L) :=
  transportWitnessRestriction (snd E K) i ≫
    (transportWitnessTotalIso (snd E L) (pullback.snd (snd E K) i)
      (productProjectionPullbackIso E i) (productProjectionPullbackIso_hom_snd E i)).hom

/-- 概要：積射影の表現の制限は周囲の四角形の同じ制限を回収する。
方針：表現空間の制限と全空間の同型の二つの包含公式を続ける。
規約：全高次単体での射の等式。
使われ方：点上の族の比較との自然性。 -/
lemma pointProductWitnessPre_ι (E : SSet.{u + 1}) [KanComplex E]
    {K L : SSet.{u + 1}} (i : L ⟶ K) :
    pointProductWitnessPre E i ≫ transportWitnessSpaceι (snd E L) =
      transportWitnessSpaceι (snd E K) ≫ pointProductSquarePre E i := by
  dsimp only [pointProductWitnessPre, pointProductSquarePre]
  rw [Category.assoc, transportWitnessTotalIso_hom_ι, ← Category.assoc,
    transportWitnessRestriction_ι, Category.assoc]

/-- 概要：点上の表現の族の同型は実際のパラメーター制限に自然。
方針：表現空間の包含後に四角形の自然性を適用する。
規約：区間や境界も含む任意のパラメーターを扱う。
使われ方：区間境界制限を点上の表現空間の区間族の境界制限へ移す。 -/
lemma pointProductWitnessTensorIso_hom_naturality (E : SSet.{u + 1}) [KanComplex E]
    {K L : SSet.{u + 1}} (i : L ⟶ K) :
    pointProductWitnessPre E i ≫ (pointProductWitnessTensorIso E L).hom =
      (pointProductWitnessTensorIso E K).hom ≫
        (pre i).app (transportWitnessSpace (transportPointProjection E)) := by
  let : Mono (transportWitnessSpaceι (transportPointProjection E)) := inferInstanceAs
    (Mono (fullSubcomplexOnVertices (transportSquareSpace (transportPointProjection E))
      (IsTransportWitnessVertex (transportPointProjection E))).ι)
  have : Mono ((ihom L).map (transportWitnessSpaceι (transportPointProjection E))) :=
    (ihom L).map_mono _
  apply (cancel_mono ((ihom L).map (transportWitnessSpaceι (transportPointProjection E)))).1
  rw [Category.assoc, pointProductWitnessTensorIso_hom_ι, ← Category.assoc,
    pointProductWitnessPre_ι]
  simp only [Category.assoc]
  rw [pointProductSquareTensorIso_hom_naturality, pre_comm_ihom_map]
  simp only [← Category.assoc]
  rw [pointProductWitnessTensorIso_hom_ι]

end SerrePositivity.InfinityCategories
