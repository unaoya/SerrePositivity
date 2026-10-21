module

public import SerrePositivity.InfinityCategories.F2.FunctorTriangleFirstMiddleComparison
public import SerrePositivity.InfinityCategories.F2.FunctorTriangleInitialNativeIdentity

/-!
概要：元の同じ中間比較は、第一作用の頂点へ表示を揃えると元の第一始域比較の逆となる。
方針：第一辺の固定始点の恒等性と canonical 第一辺の恒等性を指定自然性へ適用する。
規約：元の指定同型を保持。使われ方：全終点比較を元の二辺の比較へ表す。
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
local notation "u" => functorHomotopySourceCanonicalWitness a p s hi

/-- 元の指定三角形の実中間頂点は、同じ第一普遍作用の頂点そのもの。 -/
lemma functorTriangleCanonical_middle_first_vertex :
    relativeFunctorVertex (leftUnstraighteningProjection G) p (z).middle (z).middle_projection =
      relativeFunctorVertex (leftUnstraighteningProjection G) p (u).endpoint (u).endpoint_over := by
  apply Subtype.ext
  exact congrArg functorVertex (functorTriangleCanonical_middle T p s hi)

/-- 同じ元の中間比較を、同じ第一作用の実終点の表示へ揃えた値。 -/
def FunctorTrianglePointedWitness.firstEndpointComparison :=
  vertexIsoOfEq (w.middleComparison hi) rfl
    (functorTriangleCanonical_middle_first_vertex (T := T) (p := p) (s := s) hi)

/-- 元の第一始域比較と同じ中間比較は、元の第一作用の頂点で厳密に相殺する。 -/
lemma FunctorTrianglePointedWitness.firstEndpointComparison_cancel :
    functorHomotopySourceEndpointIso a p s hi w.firstWitness ≪≫
      w.firstEndpointComparison hi = Iso.refl _ := by
  have hs := functorHomotopyPrismSpecified_naturality a p s s hi hi w.firstWitness
    (z).firstWitness (w.firstPrismComparison hi)
  change w.firstNativeComparison hi ≪≫
    functorHomotopySourceEndpointIso a p s hi (z).firstWitness =
    functorHomotopySourceEndpointIso a p s hi w.firstWitness ≪≫ w.firstActualComparison hi at hs
  rw [w.firstNativeComparison_eq_refl hi, w.firstActualComparison_eq_middle hi] at hs
  have hv := functorTriangleCanonical_middle_first_vertex (T := T) (p := p) (s := s) hi
  have hw := functorTriangleCanonical_firstWitness T p s hi
  have hc := functorHomotopySourceEndpointIso_heq_refl a p s hi (z).firstWitness
    (congrArg RelativeExtensionEndpointWitness.extension hw)
    (congrArg RelativeExtensionEndpointWitness.endpoint hw)
  have he := vertexIso_square_of_heq (Iso.refl _)
    (functorHomotopySourceEndpointIso a p s hi (z).firstWitness)
    (functorHomotopySourceEndpointIso a p s hi w.firstWitness) (w.middleComparison hi)
    (Iso.refl _) (Iso.refl _)
    (functorHomotopySourceEndpointIso a p s hi w.firstWitness) (w.firstEndpointComparison hi)
    rfl rfl rfl hv (HEq.rfl) hc (HEq.rfl) (vertexIsoOfEq_heq _ rfl hv).symm hs
  simpa only [Iso.refl_trans] using he.symm

/-- 同じ元の中間比較は、元の指定第一始域比較の逆そのもの。 -/
lemma FunctorTrianglePointedWitness.firstEndpointComparison_eq_symm :
    w.firstEndpointComparison hi = (functorHomotopySourceEndpointIso a p s hi
      w.firstWitness).symm := by
  let β := functorHomotopySourceEndpointIso a p s hi w.firstWitness
  have hc := congrArg (fun f => β.inv ≫ f)
    (congrArg Iso.hom (w.firstEndpointComparison_cancel hi))
  change β.inv ≫ (β.hom ≫ (w.firstEndpointComparison hi).hom) = β.inv ≫ 𝟙 _ at hc
  apply Iso.ext
  change (w.firstEndpointComparison hi).hom = β.inv
  simpa only [Iso.trans_hom, Iso.refl_hom, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp, Category.comp_id] using hc

end SerrePositivity.InfinityCategories.F2
