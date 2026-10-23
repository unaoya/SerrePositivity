module

public import SerrePositivity.InfinityCategories.F1.Universe.SmallFiberWitnessContractible
public import SerrePositivity.InfinityCategories.F1.Universe.SmallCartesianRepresentationExtension

/-!
概要：小さい次数 fiber の表現の延長を任意の cartesian な全空間表示へ移す。
方針：標準 pullback の制限と全空間の同型の合成に全境界充填を移す。
規約：底と全空間の小ささを仮定しない。
使われ方：任意の底上の collage の指定両端の延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：小さい次数 fiber の cartesian な単射制限は trivial Kan fibration。
方針：標準 pullback の制限と全空間の同型へ分解する。
規約：全空間の小ささは不要。
使われ方：指定した具体的な境界上の全ての族の延長。 -/
lemma smallFiberTransportWitnessPre_trivialKanFibration {p q : Arrow SSet.{u + 1}}
    [LeftFibration p.hom] [LeftFibration q.hom] (hq : HasSmallSimplexFibers q.hom)
    (f : p ⟶ q) (hf : IsPullback f.left p.hom q.hom f.right) [Mono f.right] :
    TrivialKanFibration (transportWitnessPre f hf) := by
  rw [transportWitnessPre_eq_restriction_totalIso f hf]
  exact ⟨trivialKanFibrations.comp_mem _ _
    (smallFiberTransportWitnessRestriction_trivialKanFibration q.hom hq f.right).mem
    (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 概要：具体的な cartesian 境界の指定表現を延長する空間は可縮 Kan。
方針：前合成の trivial Kan fibration の fiber を取る。
規約：全空間の表示やパラメーターの大きさに依存しない。
使われ方：指定した両端を保つ collage 表現の比較。 -/
lemma smallFiberCartesianRepresentationExtension_isContractibleKan {p q : Arrow SSet.{u + 1}}
    [LeftFibration p.hom] [LeftFibration q.hom] (hq : HasSmallSimplexFibers q.hom)
    (f : p ⟶ q) (hf : IsPullback f.left p.hom q.hom f.right) [Mono f.right]
    (R : LeftTransportRepresentation p.hom) :
    IsContractibleKan (vertexFiber (transportWitnessPre f hf) (transportWitnessVertex R)) := by
  have := smallFiberTransportWitnessPre_trivialKanFibration hq f hf
  exact vertexFiber_isContractibleKan _ _

/-- 概要：cartesian な単射の指定表現は小さい次数 fiber の元の射影へ厳密に延長できる。
方針：表現空間の前合成の切断を実際の表現へ戻す。
規約：底と全空間は大きくてもよい。
使われ方：collage の両端を同時に厳密に指定する。 -/
lemma exists_smallFiber_cartesianTransportRepresentation_extension {p q : Arrow SSet.{u + 1}}
    [LeftFibration p.hom] [LeftFibration q.hom] (hq : HasSmallSimplexFibers q.hom)
    (f : p ⟶ q) (hf : IsPullback f.left p.hom q.hom f.right) [Mono f.right]
    (R : LeftTransportRepresentation p.hom) :
    ∃ S : LeftTransportRepresentation q.hom, S.cartesianRestrict f.left f.right hf = R := by
  have := smallFiberTransportWitnessPre_trivialKanFibration hq f hf
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section (transportWitnessPre f hf)
  obtain ⟨S, hS⟩ := transportWitnessVertex_surjective _ (s.app _ (transportWitnessVertex R))
  refine ⟨S, transportWitnessVertex_injective _ ?_⟩
  rw [← transportWitnessPre_cartesianRestrict_vertex, hS]
  exact congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) (transportWitnessVertex R)) hs

end SerrePositivity.InfinityCategories
