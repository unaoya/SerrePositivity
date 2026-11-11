module

public import SerrePositivity.KST.Spectra.MappingCorner
public import SerrePositivity.KST.Spectra.PushoutProductMonomorphism
public import SerrePositivity.KST.NonConnective.SequentialLatchingHom

/-!
概要：全スペクトルの二変数 corner の段ごとの相対充填を構成する。
方針：源の相対 latching 単射と標的の全単射 RLP を点つき mapping corner に適用する。
規約：元の部分パラメータ・源の指定部分・標的射影を全て厳密に保持する。
使われ方：相対 BF 置換の右射影を含む全 Hom 自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 概要：源が単射、標的が全単射 RLP のとき元の mapping corner も全単射 RLP。
方針：二つの単射の pushout-product の単射性を使う。
規約：Kan 性とモデル圏 instance を仮定しない。
使われ方：全スペクトル段の相対充填。 -/
lemma corner_rlp_monomorphisms {A X E Z : PointedSimplicialSet.{u}}
    (i : A ⟶ X) [Mono i.right] (p : E ⟶ Z)
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (corner i p) := by
  intro T U j hj
  let : Mono j := hj
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i.right j
  exact corner_hasLiftingProperty i p j (hp pp.ι (PushoutProductMonomorphism.mono pp))

/-- 概要：指定した部分族・源上の族・標的の族を同時に保つ点つき Hom の充填。
方針：元の mapping corner の実引き戻しへ底の二族を束ね、全単射 RLP を使う。
規約：出力は元の Hom の族であり、三つの境界式を厳密に満たす。
使われ方：零段と相対 latching 対象での共通の充填。 -/
lemma corner_family_lift {A X E Z : PointedSimplicialSet.{u}}
    (i : A ⟶ X) [Mono i.right] (p : E ⟶ Z)
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right)
    {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
    (a : T ⟶ (PointedObject.basedHom X E).right)
    (b : U ⟶ (PointedObject.basedHom X Z).right)
    (c : U ⟶ (PointedObject.basedHom A E).right)
    (hbc : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Z = c ≫ (PointedObject.basedHomMap A p).right)
    (ha : a ≫ (PointedObject.basedHomMap X p).right = j ≫ b)
    (hc : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i E = j ≫ c) :
    ∃ l : U ⟶ (PointedObject.basedHom X E).right,
      j ≫ l = a ∧ l ≫ (PointedObject.basedHomMap X p).right = b ∧
        l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i E = c := by
  let t : U ⟶ cornerTarget i p := pullback.lift b c hbc
  let : HasLiftingProperty j (corner i p) := corner_rlp_monomorphisms i p hp j inferInstance
  let sq : CommSq a j (corner i p) t := ⟨by
    apply pullback.hom_ext
    · simpa only [Category.assoc, corner_fst, t, pullback.lift_fst] using ha
    · simpa only [Category.assoc, corner_snd, t, pullback.lift_snd] using hc⟩
  refine ⟨sq.lift, sq.fac_left, ?_, ?_⟩
  · have h := congrArg (· ≫ pullback.fst _ _) sq.fac_right
    simpa only [Category.assoc, corner_fst, t, pullback.lift_fst] using h
  · have h := congrArg (· ≫ pullback.snd _ _) sq.fac_right
    simpa only [Category.assoc, corner_snd, t, pullback.lift_snd] using h

end SerrePositivity.KST.Spectra.PointedMapping
