module

public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationFamilyWitness
public import SerrePositivity.InfinityCategories.F1.Coherent.SmallCoherentFamilyUniqueness

/-!
概要：一般の選択表現の間の相対射の族の実現の一意性。
方針：指定端点の collage による比較を族全体の変換空間へ戻す。
規約：実現の構成から一意性の依存を分離する。
使われ方：straightening の写像空間の比較の選択独立性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：同じ相対射の族の二つの実現は変換の族全体で関手同型。
方針：積の底上の指定表現の coherent な実現の一意性へ戻す。
規約：次数 fiber の小ささを明示し底やパラメーターは任意。
使われ方：写像空間の比較の選択独立性。 -/
lemma TransportRepresentationFamilyWitness.unique {E F B K : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} [LeftFibration p] [LeftFibration q]
    {R : LeftTransportRepresentation p} {S : LeftTransportRepresentation q}
    (hp : HasSmallSimplexFibers p) (hq : HasSmallSimplexFibers q)
    {t t' : K ⟶ leftUnstraighteningTransformationSpace R.diagram S.diagram} {f : E ⊗ K ⟶ F}
    (hf : f ≫ q = fst E K ≫ p)
    (w : TransportRepresentationFamilyWitness R S t f)
    (w' : TransportRepresentationFamilyWitness R S t' f) : Nonempty (FunctorIso t t') := by
  have hs : prismEndpoint 0 (E ⊗ K) ≫ w.leftPrism = fst E K ≫ R.pointedMap := by
    rw [TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      prismEndpoint_associator_inv]
    exact w.source
  have ht : prismEndpoint 1 (E ⊗ K) ≫ w.leftPrism = f ≫ S.pointedMap := by
    rw [TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      prismEndpoint_associator_inv]
    exact w.target
  have hs' : prismEndpoint 0 (E ⊗ K) ≫ w'.leftPrism = fst E K ≫ R.pointedMap := by
    rw [TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      prismEndpoint_associator_inv]
    exact w'.source
  have ht' : prismEndpoint 1 (E ⊗ K) ≫ w'.leftPrism = f ≫ S.pointedMap := by
    rw [TransportRepresentationFamilyWitness.leftPrism, ← Category.assoc,
      prismEndpoint_associator_inv]
    exact w'.target
  obtain ⟨e⟩ := coherentFamily_uniqueness_of_small_fibers p q f hf hp hq R S
    (coherentTransformationFamilyDiagram t) (coherentTransformationFamilyDiagram t')
    (coherentTransformationFamilyDiagram_zero t) (coherentTransformationFamilyDiagram_one t)
    (coherentTransformationFamilyDiagram_zero t') (coherentTransformationFamilyDiagram_one t')
    w.leftPrism w'.leftPrism hs ht hs' ht' w.leftPrism_projection w'.leftPrism_projection
  rw [coherentTransformationFamilyDiagram_curry, coherentTransformationFamilyDiagram_curry] at e
  exact ⟨e⟩

end SerrePositivity.InfinityCategories
