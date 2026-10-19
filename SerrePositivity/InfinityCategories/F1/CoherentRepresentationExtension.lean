module

public import SerrePositivity.InfinityCategories.F1.SmallRepresentationExtension
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningSmallness

/-!
概要：任意の coherent な空間値図式の unstraightening の相対表現を延長する。
方針：既証明の unstraightening の小ささを一般の単射の延長定理へ渡す。
規約：底は各次数で小さく図式に strict 性や通常の nerve の仮定を加えない。
使われ方：Kerodon §5.6.5 の coherent 比較の主経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

local instance coherentExtensionPullbackSndLF {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) : LeftFibration (pullback.snd p g) :=
  ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩

/-- 概要：任意の coherent 空間値図式の unstraightening の表現空間は可縮。
方針：unstraightening の次数ごとの小ささから一般の可縮性定理を適用する。
規約：底を通常の圏の nerve に限定しない。
使われ方：coherent な図式の復元の選択空間の主経路。 -/
lemma coherentUnstraighteningWitnessSpace_isContractibleKan {B : SSet.{u + 1}}
    [∀ m, Small.{u} (B.obj m)] (F : B ⟶ SpaceInfinity.{u}) :
    IsContractibleKan (transportWitnessSpace (leftUnstraighteningProjection F)) :=
  smallTransportWitnessSpace_isContractibleKan (leftUnstraighteningProjection F)

/-- 概要：coherent な図式の unstraightening の部分底上の表現を厳密に延長する。
方針：unstraightening の小ささを任意の単射への相対存在へ適用する。
規約：分類図式と全空間の写像をともに固定する。
使われ方：Kerodon Theorem 5.6.5.12 の小さい底の coherent 図式への適用。 -/
lemma exists_coherentUnstraighteningRepresentation_extension {B D : SSet.{u + 1}}
    [∀ m, Small.{u} (B.obj m)] (F : B ⟶ SpaceInfinity.{u}) (g : D ⟶ B) [Mono g]
    (R : LeftTransportRepresentation (pullback.snd (leftUnstraighteningProjection F) g)) :
    ∃ S : LeftTransportRepresentation (leftUnstraighteningProjection F), S.restrict g = R :=
  exists_small_leftTransportRepresentation_extension (leftUnstraighteningProjection F) g R

/-- 概要：指定した部分底上の表現を延長する空間は coherent な図式でも可縮。
方針：unstraightening の小ささを全高次の相対一意性に適用する。
規約：頂点の一意性だけに弱めない。
使われ方：coherent 比較の境界固定の選択独立性。 -/
lemma coherentUnstraighteningRepresentationExtension_isContractibleKan {B D : SSet.{u + 1}}
    [∀ m, Small.{u} (B.obj m)] (F : B ⟶ SpaceInfinity.{u}) (g : D ⟶ B) [Mono g]
    (R : LeftTransportRepresentation (pullback.snd (leftUnstraighteningProjection F) g)) :
    IsContractibleKan (vertexFiber (transportWitnessRestriction (leftUnstraighteningProjection F) g)
      (transportWitnessVertex R)) :=
  smallTransportRepresentationExtension_isContractibleKan (leftUnstraighteningProjection F) g R

end SerrePositivity.InfinityCategories
