module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopySourceComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionEndpointIdentity

/-!
概要：元の普遍 prism の同じ実制限では、F1 の指定始域比較は恒等となる。
方針：同じ実延長・実終点の証拠の等式を回収し、指定終点比較の恒等則を使う。
規約：比較を選び直さない。使われ方：元の指定三角形の右辺への自然性の適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
  (H : SSet.Homotopy F G) (p : C ⟶ B) (s : C ⟶ leftUnstraightening F)
  (hi : s ≫ leftUnstraighteningProjection F = p)
local notation "z" => functorHomotopySourceCanonicalWitness H p s hi

/-- 同じ元の普遍 prism の指定始域比較は、選択済み作用の頂点の恒等同型。 -/
lemma functorHomotopySourceEndpointIso_canonical :
    functorHomotopySourceEndpointIso H p s hi z = Iso.refl _ :=
  RelativeExtensionEndpointWitness.iso_refl z (prismEndpoint_zero_leftAnodyne C)
    (z).initial_base (z).endpoint_base

/-- 普遍 prism と実延長・実終点が同じなら、元の指定比較は同じ恒等同型となる。 -/
lemma functorHomotopySourceEndpointIso_heq_refl
    (w : RelativeExtensionEndpointWitness pointedSpaceProjection
      ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)) (prismEndpoint 0 C)
      (s ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p)
    (he : w.extension = (z).extension) (hg : w.endpoint = (z).endpoint) :
    HEq (functorHomotopySourceEndpointIso H p s hi w)
      (Iso.refl (SSet.HomotopyCategory.mk
        (relativeFunctorVertex (leftUnstraighteningProjection G) p
          (z).endpoint (z).endpoint_over))) := by
  have hw := w.eq_of_extension_endpoint z he hg
  subst w
  exact heq_of_eq (functorHomotopySourceEndpointIso_canonical H p s hi)

end SerrePositivity.InfinityCategories.F2
