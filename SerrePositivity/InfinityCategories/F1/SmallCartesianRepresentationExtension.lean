module

public import SerrePositivity.InfinityCategories.F1.TransportRepresentationCartesianRestriction
public import SerrePositivity.InfinityCategories.F1.TransportWitnessCartesianRestriction
public import SerrePositivity.InfinityCategories.F1.SmallRepresentationExtension

/-!
概要：小さい全空間の表現の境界固定延長を任意の cartesian な表示に移す。
方針：標準 pullback への制限と全空間の同型で表現空間の全境界充填を移す。
規約：指定した全空間の上の表現を厳密に回収する。
使われ方：相対射の区間実現で両端の和に指定した表現を延長する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：cartesian 制限の表現の頂点は表現空間の前合成と一致する。
方針：周囲の四角形へ含めて図式と pointed space への射を比較する。
規約：pullback の表示の選択を隠さず両射を保つ。
使われ方：空間上の充填から実際の表現の厳密な延長へ戻す。 -/
lemma transportWitnessPre_cartesianRestrict_vertex {p q : Arrow SSet.{u + 1}}
    [LeftFibration p.hom] [LeftFibration q.hom] (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) (R : LeftTransportRepresentation q.hom) :
    (transportWitnessPre f hf).app _ (transportWitnessVertex R) =
      transportWitnessVertex (R.cartesianRestrict f.left f.right hf) := by
  apply Subtype.ext
  have h := congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) (transportWitnessVertex R))
    (transportWitnessPre_ι f hf)
  change _ = (transportSquarePre f).app _ (transportSquareVertex R.toSquare) at h
  refine h.trans ?_
  rw [transportSquarePre_vertex]
  apply congrArg transportSquareVertex
  apply LeftTransportSquare.ext
  · rfl
  · exact (R.cartesianRestrict_pointedMap _ _ hf).symm

/-- 概要：小さい全空間の cartesian な単射制限は trivial Kan fibration。
方針：標準 pullback への制限の全境界充填を同型で移す。
規約：底の小ささや境界の表現の存在は仮定しない。
使われ方：両端の和などの具体的な全空間の上の相対延長。 -/
lemma smallTransportWitnessPre_trivialKanFibration {p q : Arrow SSet.{u + 1}}
    [LeftFibration p.hom] [LeftFibration q.hom] [∀ n, Small.{u} (q.left.obj n)]
    (f : p ⟶ q) (hf : IsPullback f.left p.hom q.hom f.right) [Mono f.right] :
    TrivialKanFibration (transportWitnessPre f hf) := by
  rw [transportWitnessPre_eq_restriction_totalIso f hf]
  exact ⟨trivialKanFibrations.comp_mem _ _
    (smallTransportWitnessRestriction_trivialKanFibration q.hom f.right).mem
    (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 概要：cartesian な単射の上の指定表現を元の小さい全空間へ厳密に延長する。
方針：表現空間の前合成の切断を実際の表現の頂点の全単射へ移す。
規約：標準 pullback の全空間へ指定表現を置き換える必要はない。
使われ方：指定した両端表現から区間実現の表現を得る。 -/
lemma exists_small_cartesianTransportRepresentation_extension {p q : Arrow SSet.{u + 1}}
    [LeftFibration p.hom] [LeftFibration q.hom] [∀ n, Small.{u} (q.left.obj n)]
    (f : p ⟶ q) (hf : IsPullback f.left p.hom q.hom f.right) [Mono f.right]
    (R : LeftTransportRepresentation p.hom) :
    ∃ S : LeftTransportRepresentation q.hom, S.cartesianRestrict f.left f.right hf = R := by
  have := smallTransportWitnessPre_trivialKanFibration f hf
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section (transportWitnessPre f hf)
  obtain ⟨S, hS⟩ := transportWitnessVertex_surjective _ (s.app _ (transportWitnessVertex R))
  refine ⟨S, transportWitnessVertex_injective _ ?_⟩
  rw [← transportWitnessPre_cartesianRestrict_vertex, hS]
  exact congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) (transportWitnessVertex R)) hs

end SerrePositivity.InfinityCategories
