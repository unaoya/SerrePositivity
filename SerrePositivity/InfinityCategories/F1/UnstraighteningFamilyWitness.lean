module

public import SerrePositivity.InfinityCategories.F1.CoherentTransformationFamilyDiagram
public import SerrePositivity.InfinityCategories.F1.SmallCoherentFamilyUniqueness
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningSmallness

/-!
概要：相対射の族を表す coherent な変換の pointed な持ち上げを束ねる。
方針：始点・終点・底を同時に保つ prism を記録する。
規約：相対射の族自体は明示した入力として保持する。
使われ方：写像空間比較の両側の逆の整合性の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：指定した相対射の族を変換の族が実現する pointed な証拠。
方針：全パラメーターでの prism の三条件を記録する。
規約：可逆性を要求しない。
使われ方：普遍的な復元と選択した持ち上げを共通の型で比較する。 -/
structure UnstraighteningFamilyWitness {B K : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (t : K ⟶ leftUnstraighteningTransformationSpace F G)
    (f : leftUnstraightening F ⊗ K ⟶ leftUnstraightening G) where
  prism : ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗ K ⟶ PointedSpaceInfinity.{u}
  source : (prismEndpoint 0 (leftUnstraightening F) ▷ K) ≫ prism =
    fst (leftUnstraightening F) K ≫ pullback.fst pointedSpaceProjection F
  target : (prismEndpoint 1 (leftUnstraightening F) ▷ K) ≫ prism =
    f ≫ pullback.fst pointedSpaceProjection G
  projection : prism ≫ pointedSpaceProjection =
    ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ K) ≫
      functorParameterizedPrism (intervalMappingUncurry t)

/-- 概要：証拠の prism を区間を左に出した積の表示にする。
方針：結合子の逆で前合成する。
規約：元の全空間とパラメーターをともに保持する。
使われ方：積の底上の collage による比較。 -/
def UnstraighteningFamilyWitness.leftPrism {B K : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}} {t : K ⟶ leftUnstraighteningTransformationSpace F G}
    {f : leftUnstraightening F ⊗ K ⟶ leftUnstraightening G}
    (w : UnstraighteningFamilyWitness F G t f) :
    (Δ[1] : SSet.{u + 1}) ⊗ (leftUnstraightening F ⊗ K) ⟶ PointedSpaceInfinity.{u} :=
  (α_ Δ[1] (leftUnstraightening F) K).inv ≫ w.prism

/-- 概要：区間を左に出した証拠は元の図式の族を被覆する。
方針：結合子の自然性と証拠の射影条件を使う。
規約：全てのパラメーターで厳密に可換。
使われ方：coherent な実現の族の一意性への入力。 -/
lemma UnstraighteningFamilyWitness.leftPrism_projection {B K : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}} {t : K ⟶ leftUnstraighteningTransformationSpace F G}
    {f : leftUnstraightening F ⊗ K ⟶ leftUnstraightening G}
    (w : UnstraighteningFamilyWitness F G t f) :
    w.leftPrism ≫ pointedSpaceProjection =
      (Δ[1] ◁ (leftUnstraighteningProjection F ▷ K)) ≫ coherentTransformationFamilyDiagram t := by
  rw [UnstraighteningFamilyWitness.leftPrism, Category.assoc, w.projection, ← Category.assoc]
  have hn : (α_ (Δ[1] : SSet.{u + 1}) (leftUnstraightening F) K).inv ≫
      ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ K) =
      (Δ[1] ◁ (leftUnstraighteningProjection F ▷ K)) ≫ (α_ Δ[1] B K).inv := by
    apply SSet.hom_ext; intro n; rfl
  rw [hn, Category.assoc]
  rfl

/-- 概要：同じ小さい相対射の族を表す二つの変換の族は関手同型。
方針：pointed な証拠を collage の比較へ渡して元の変換の射を回収する。
規約：底とパラメーターは各次数で小さい。
使われ方：写像空間比較の左逆の全体での検証。 -/
lemma UnstraighteningFamilyWitness.small_unique {B K : SSet.{u + 1}}
    [∀ n, Small.{u} (B.obj n)] [∀ n, Small.{u} (K.obj n)]
    {F G : B ⟶ SpaceInfinity.{u}} {t t' : K ⟶ leftUnstraighteningTransformationSpace F G}
    {f : leftUnstraightening F ⊗ K ⟶ leftUnstraightening G}
    (hf : f ≫ leftUnstraighteningProjection G =
      fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F)
    (w : UnstraighteningFamilyWitness F G t f) (w' : UnstraighteningFamilyWitness F G t' f) :
    Nonempty (FunctorIso t t') := by
  have hsource : prismEndpoint 0 (leftUnstraightening F ⊗ K) ≫ w.leftPrism =
      fst (leftUnstraightening F) K ≫ pullback.fst pointedSpaceProjection F := by
    rw [UnstraighteningFamilyWitness.leftPrism, ← Category.assoc, prismEndpoint_associator_inv]
    exact w.source
  have htarget : prismEndpoint 1 (leftUnstraightening F ⊗ K) ≫ w.leftPrism =
      f ≫ pullback.fst pointedSpaceProjection G := by
    rw [UnstraighteningFamilyWitness.leftPrism, ← Category.assoc, prismEndpoint_associator_inv]
    exact w.target
  have hsource' : prismEndpoint 0 (leftUnstraightening F ⊗ K) ≫ w'.leftPrism =
      fst (leftUnstraightening F) K ≫ pullback.fst pointedSpaceProjection F := by
    rw [UnstraighteningFamilyWitness.leftPrism, ← Category.assoc, prismEndpoint_associator_inv]
    exact w'.source
  have htarget' : prismEndpoint 1 (leftUnstraightening F ⊗ K) ≫ w'.leftPrism =
      f ≫ pullback.fst pointedSpaceProjection G := by
    rw [UnstraighteningFamilyWitness.leftPrism, ← Category.assoc, prismEndpoint_associator_inv]
    exact w'.target
  obtain ⟨e⟩ := small_coherentFamily_uniqueness (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection G) f hf (unstraighteningTransportRepresentation F)
    (unstraighteningTransportRepresentation G)
    (coherentTransformationFamilyDiagram t) (coherentTransformationFamilyDiagram t')
    (coherentTransformationFamilyDiagram_zero t) (coherentTransformationFamilyDiagram_one t)
    (coherentTransformationFamilyDiagram_zero t') (coherentTransformationFamilyDiagram_one t')
    w.leftPrism w'.leftPrism
    (by simpa only [unstraighteningTransportRepresentation, LeftTransportRepresentation.pointedMap,
      Category.id_comp] using hsource)
    (by simpa only [unstraighteningTransportRepresentation, LeftTransportRepresentation.pointedMap,
      Category.id_comp] using htarget)
    (by simpa only [unstraighteningTransportRepresentation, LeftTransportRepresentation.pointedMap,
      Category.id_comp] using hsource')
    (by simpa only [unstraighteningTransportRepresentation, LeftTransportRepresentation.pointedMap,
      Category.id_comp] using htarget') w.leftPrism_projection w'.leftPrism_projection
  rw [coherentTransformationFamilyDiagram_curry, coherentTransformationFamilyDiagram_curry] at e
  exact ⟨e⟩

end SerrePositivity.InfinityCategories
