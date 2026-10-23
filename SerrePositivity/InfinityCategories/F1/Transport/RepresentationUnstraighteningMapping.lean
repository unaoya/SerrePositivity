module

public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationMappingSpaceMap
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.UnstraighteningFamilyWitnessRestriction

/-!
概要：一般の表現の写像空間の比較は標準 unstraightening 上で実際の逆を持つ。
方針：普遍族の証拠と既存の unstraightening の普遍持ち上げを比較する。
規約：逆射は元の unstraightening の比較射そのもの。
使われ方：straightening の写像空間の作用と既存の比較の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：標準表現の比較射は元の unstraightening の比較を逆とする写像空間の同値。
方針：一般の復元の普遍的証拠と unstraightening の普遍的証拠を全体で比較する。
規約：基底の小ささや quasicategory 性を要求しない。
使われ方：一般の straightening の比較の標準表現上での検証。 -/
def transportRepresentationUnstraighteningMappingEquivalence {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    QCatEquivalence
      (relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F))
      (leftUnstraighteningTransformationSpace F G) := by
  let Y := relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
  let T := leftUnstraighteningTransformationSpace F G
  let M := leftUnstraighteningMappingSpaceMap F G
  let R := unstraighteningTransportRepresentation F
  let S := unstraighteningTransportRepresentation G
  let hp := leftUnstraighteningProjection_hasSmallSimplexFibers F
  let hq := leftUnstraighteningProjection_hasSmallSimplexFibers G
  let N := transportRepresentationMappingSpaceMap hp hq R S
  have wl := transportRepresentationMappingFamilyWitness hp hq R S M
  have hleft : Nonempty (FunctorIso (M ≫ N) (𝟙 T)) :=
    TransportRepresentationFamilyWitness.unique (R := R) (S := S)
      hp hq (relativeFunctorUncurry_projection M) wl
      (unstraighteningUniversalFamilyWitness F G).toRepresentationWitness
  let f := relativeFunctorUncurry (𝟙 Y)
  have hf := relativeFunctorUncurry_projection (𝟙 Y)
  have w := transportRepresentationMappingSpaceWitness hp hq R S
  have hright := unstraighteningFamilyComparisonIso F G N f hf
    w.prism w.source w.target w.projection
  have hc : relativeFunctorCurry f hf = 𝟙 Y := by
    apply relativeFunctorUncurry_injective (leftUnstraighteningProjection G)
      (leftUnstraighteningProjection F)
    exact relativeFunctorUncurry_curry f hf
  rw [hc] at hright
  exact { hom := N, inv := M, homInvIso := hright, invHomIso := hleft.some }

/-- 概要：標準表現上の一般の写像空間比較射そのものは同値。
方針：明示的な逆を持つ比較の同値データを使う。
規約：新しい同値な射へ取り替えない。
使われ方：一般の表現の比較の同値性への還元。 -/
lemma transportRepresentationMappingSpaceMap_unstraightening_isQCatEquivalence
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence (transportRepresentationMappingSpaceMap
      (leftUnstraighteningProjection_hasSmallSimplexFibers F)
      (leftUnstraighteningProjection_hasSmallSimplexFibers G)
      (unstraighteningTransportRepresentation F) (unstraighteningTransportRepresentation G)) :=
  (transportRepresentationUnstraighteningMappingEquivalence F G).isQCatEquivalence

end SerrePositivity.InfinityCategories
