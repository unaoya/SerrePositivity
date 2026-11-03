module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleRightMiddleComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleFirstEndpointNormalized

/-!
概要：元の全終点比較を、同じ元の第二比較の逆と中間比較の native 後合成で表す。
方針：右辺の指定自然性を相殺し、第一辺の中間比較の逆の式も保持する。
規約：指定比較の値を保持。使われ方：全終点比較を元の二辺の比較へ表す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle a b c} {p : C ⟶ B} {s : C ⟶ leftUnstraightening F}
  (w : FunctorTrianglePointedWitness T p s) (hi : s ≫ leftUnstraighteningProjection F = p)
local notation "z" => functorTrianglePointedCanonicalWitness T p s hi
local notation "P" => HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection G)
  (leftUnstraighteningProjection J)
  (Subtype.val (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)))
  (Subtype.property (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b))) p

/-- 全終点比較は、元の第二指定始域比較の逆と、同じ中間比較の native 後合成で表せる。 -/
lemma FunctorTrianglePointedWitness.rightEndpointComparison_eq_edges :
    w.rightEndpointComparison hi =
      (functorHomotopySourceEndpointIso b p w.middle w.middle_projection w.secondWitness).symm ≪≫
        w.middleNativeComparison hi := by
  let β := functorHomotopySourceEndpointIso b p w.middle w.middle_projection w.secondWitness
  have h := congrArg (fun e => β.inv ≫ e)
    (congrArg Iso.hom (w.middleNativeComparison_eq hi))
  change β.inv ≫ (w.middleNativeComparison hi).hom =
    β.inv ≫ (β.hom ≫ (w.rightEndpointComparison hi).hom) at h
  apply Iso.ext
  simpa only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp] using h.symm

/-- 中間比較の native 後合成は、元の第一指定始域比較の逆の同じ後合成の値。 -/
lemma FunctorTrianglePointedWitness.middleNativeComparison_heq_firstInverse :
    HEq (w.middleNativeComparison hi)
      (VertexIso.map (functorHomotopySourceEndpointIso a p s hi w.firstWitness).symm P) := by
  have hv := functorTriangleCanonical_middle_first_vertex (T := T) (p := p) (s := s) hi
  have he := vertexIso_map_heq_of_heq (w.middleComparison hi) (w.firstEndpointComparison hi)
    rfl hv (vertexIsoOfEq_heq _ rfl hv).symm P
  rw [w.firstEndpointComparison_eq_symm hi] at he
  exact (vertexIsoOfEq_heq _
    (relativeFunctorPost_vertex _ _ _
      (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).property
      p w.middle w.middle_projection)
    (relativeFunctorPost_vertex _ _ _
      (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).property
      p (z).middle (z).middle_projection)).trans he

end SerrePositivity.InfinityCategories.F2
