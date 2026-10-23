module

public import SerrePositivity.InfinityCategories.F1.Universe.SmallFiberWitnessContractible
public import SerrePositivity.InfinityCategories.F1.Universe.SmallRepresentationExtension
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningSmallness

/-!
概要：任意の coherent な空間値図式の unstraightening の相対表現を延長する。
方針：unstraightening の次数 fiber の小ささを一般の単射の延長定理へ渡す。
規約：底の小ささ、図式の strict 性、通常の nerve の仮定を加えない。
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
方針：unstraightening の次数 fiber の小ささから一般の可縮性定理を適用する。
規約：底を通常の圏の nerve に限定しない。
使われ方：coherent な図式の復元の選択空間の主経路。 -/
lemma coherentUnstraighteningWitnessSpace_isContractibleKan {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) :
    IsContractibleKan (transportWitnessSpace (leftUnstraighteningProjection F)) :=
  smallFiberTransportWitnessSpace_isContractibleKan (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection_hasSmallSimplexFibers F)

/-- 概要：coherent な図式の unstraightening の部分底上の表現を厳密に延長する。
方針：unstraightening の次数 fiber の小ささを任意の単射への相対存在へ適用する。
規約：分類図式と全空間の写像をともに固定する。
使われ方：Kerodon Theorem 5.6.5.12 の任意の底の coherent 図式への適用。 -/
lemma exists_coherentUnstraighteningRepresentation_extension {B D : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (g : D ⟶ B) [Mono g]
    (R : LeftTransportRepresentation (pullback.snd (leftUnstraighteningProjection F) g)) :
    ∃ S : LeftTransportRepresentation (leftUnstraighteningProjection F), S.restrict g = R :=
  exists_smallFiber_leftTransportRepresentation_extension (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection_hasSmallSimplexFibers F) g R

/-- 概要：指定した部分底上の表現を延長する空間は coherent な図式でも可縮。
方針：unstraightening の次数 fiber の小ささを全高次の相対一意性に適用する。
規約：頂点の一意性だけに弱めない。
使われ方：coherent 比較の境界固定の選択独立性。 -/
lemma coherentUnstraighteningRepresentationExtension_isContractibleKan {B D : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (g : D ⟶ B) [Mono g]
    (R : LeftTransportRepresentation (pullback.snd (leftUnstraighteningProjection F) g)) :
    IsContractibleKan (vertexFiber (transportWitnessRestriction (leftUnstraighteningProjection F) g)
      (transportWitnessVertex R)) :=
  smallFiberTransportRepresentationExtension_isContractibleKan (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection_hasSmallSimplexFibers F) g R

/-- 概要：任意の底上の coherent な図式の表現空間の単射制限は trivial Kan fibration。
方針：普遍射影の次数 fiber の小ささを一般の制限定理へ渡す。
規約：底の小ささは仮定しない。
使われ方：境界固定の全ての高次パラメーターの持ち上げ。 -/
lemma coherentUnstraighteningWitnessRestriction_trivialKanFibration {B D : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (g : D ⟶ B) [Mono g] :
    TrivialKanFibration (transportWitnessRestriction (leftUnstraighteningProjection F) g) :=
  smallFiberTransportWitnessRestriction_trivialKanFibration (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection_hasSmallSimplexFibers F) g

/-- 概要：任意の底の coherent な図式の表現の族を部分パラメーターの延長を保って延長する。
方針：一般の小さい次数 fiber の族の持ち上げを適用する。
規約：底とパラメーターの小ささは不要。
使われ方：coherent な比較の高次の相対的な貼り合わせ。 -/
lemma exists_coherentUnstraighteningWitnessFamily_lift {B D K L : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (g : D ⟶ B) [Mono g] (j : K ⟶ L) [Mono j]
    (a : K ⟶ transportWitnessSpace (leftUnstraighteningProjection F))
    (b : L ⟶ transportWitnessSpace (pullback.snd (leftUnstraighteningProjection F) g))
    (sq : CommSq a j (transportWitnessRestriction (leftUnstraighteningProjection F) g) b) :
    ∃ H : L ⟶ transportWitnessSpace (leftUnstraighteningProjection F),
      j ≫ H = a ∧ H ≫ transportWitnessRestriction (leftUnstraighteningProjection F) g = b :=
  exists_smallFiber_transportWitnessFamily_lift (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection_hasSmallSimplexFibers F) g j a b sq

end SerrePositivity.InfinityCategories
