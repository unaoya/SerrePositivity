module

public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationMappingSpaceMap
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalComparison

/-!
概要：一般の表現の恒等射の族を定値 prism で実現する。
方針：恒等変換の pointed な持ち上げと族の一意性を使う。
規約：底とパラメーターは任意の単体集合。
使われ方：straightening の写像空間の作用の単位則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 恒等変換を全パラメーター上で定値な区間の族として表す。 -/
def transportRepresentationIdentityFamily {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (K : SSet.{u + 1}) :
    K ⟶ leftUnstraighteningTransformationSpace F F :=
  intervalMappingCurryOfEndpoints (SSet.const (functorVertex F))
    (by rw [SSet.comp_const]) (by rw [SSet.comp_const])

/-- 恒等変換の族は任意のパラメーター制限と厳密に可換。 -/
lemma transportRepresentationIdentityFamily_precomp {B K L : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (i : L ⟶ K) :
    i ≫ transportRepresentationIdentityFamily F K =
      transportRepresentationIdentityFamily F L := by
  apply intervalMappingUncurry_injective
  rw [intervalMappingUncurry_precomp]
  unfold transportRepresentationIdentityFamily
  rw [intervalMappingUncurry_curryOfEndpoints, intervalMappingUncurry_curryOfEndpoints,
    SSet.comp_const]

/-- 恒等射の族は元の pointed な比較を定値に延ばして実現できる。 -/
def transportRepresentationIdentityFamilyWitness {E B : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (R : LeftTransportRepresentation p)
    (K : SSet.{u + 1}) :
    TransportRepresentationFamilyWitness R R
      (transportRepresentationIdentityFamily R.diagram K) (fst E K) where
  prism := fst (Δ[1] ⊗ E) K ≫ snd (Δ[1] : SSet.{u + 1}) E ≫ R.pointedMap
  source := by apply SSet.hom_ext; intro n; rfl
  target := by apply SSet.hom_ext; intro n; rfl
  projection := by
    rw [Category.assoc, Category.assoc, R.pointedMap_projection]
    unfold transportRepresentationIdentityFamily
    rw [intervalMappingUncurry_curryOfEndpoints]
    apply SSet.hom_ext
    intro n
    rfl

/-- 選択した写像空間比較は恒等射の族を恒等変換の族へ関手同型で送る。 -/
lemma transportRepresentationMappingSpaceMap_identityFamily {E B : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (hp : HasSmallSimplexFibers p)
    (R : LeftTransportRepresentation p) (K : SSet.{u + 1}) :
    Nonempty (FunctorIso
      (relativeFunctorCurry (fst E K) (rfl : fst E K ≫ p = fst E K ≫ p) ≫
        transportRepresentationMappingSpaceMap hp hp R R)
      (transportRepresentationIdentityFamily R.diagram K)) := by
  apply transportRepresentationMappingFamily_comparison hp hp R R
  simpa only [relativeFunctorUncurry_curry] using
    transportRepresentationIdentityFamilyWitness R K

/-- 小さい次数 fiber の選択分類についての恒等射の族の単位則。 -/
lemma smallFiberLeftStraighteningMappingSpaceMap_identityFamily {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (hp : HasSmallSimplexFibers p)
    (K : SSet.{u + 1}) :
    Nonempty (FunctorIso
      (relativeFunctorCurry (fst E K) (rfl : fst E K ≫ p = fst E K ≫ p) ≫
        smallFiberLeftStraighteningMappingSpaceMap p p hp hp)
      (transportRepresentationIdentityFamily (smallFiberLeftStraighteningDiagram p hp) K)) :=
  transportRepresentationMappingSpaceMap_identityFamily hp
    (smallFiberLeftStraighteningRepresentation p hp) K

end SerrePositivity.InfinityCategories
