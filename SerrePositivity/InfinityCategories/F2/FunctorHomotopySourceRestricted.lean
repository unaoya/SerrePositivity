module

public import SerrePositivity.InfinityCategories.F2.FunctorHomotopySourceFamilyData

/-!
概要：全係数を保つ一点代入による、指定始域比較の元の実証拠の表示。
方針：同じ延長・終点を保持し、底・初期値・終点底だけを等式で移す。
規約：指定比較を保持。使われ方：F1 の全族比較の同じ成分との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
  (H : SSet.Homotopy F G) (p : C ⟶ B) (s : C ⟶ leftUnstraightening F)
  (hi : s ≫ leftUnstraighteningProjection F = p)
  (w : RelativeExtensionEndpointWitness pointedSpaceProjection
    ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)) (prismEndpoint 0 C)
    (s ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p)

/-- 元の二証拠の実延長・実終点を、同じ一点制限の表示で保持する。 -/
def functorHomotopySourceRestrictedWitness (actual : Bool) :=
  let wSource := if actual then w else functorHomotopySourceCanonicalWitness H p s hi
  wSource.transportData (functorHomotopySourceFamily_base_restrict H p s w)
    (functorHomotopySourceFamily_initial_restrict s)
    (functorHomotopySourceFamily_apex_restrict p)

/-- 同じ一点制限の表示による、元の指定比較そのもの。 -/
def functorHomotopySourceRestrictedIso :=
  (functorHomotopySourceRestrictedWitness H p s hi w false).iso
    (functorHomotopySourceRestrictedWitness H p s hi w true)
    (prismEndpoint_zero_leftAnodyne C)
    (functorHomotopySourceRestrictedWitness H p s hi w true).initial_base
    (functorHomotopySourceRestrictedWitness H p s hi w true).endpoint_base

/-- 底と初期値の表示を揃えても、元の指定比較の値は変わらない。 -/
lemma functorHomotopySourceEndpointIso_heq_restricted :
    HEq (functorHomotopySourceEndpointIso H p s hi w)
      (functorHomotopySourceRestrictedIso H p s hi w) :=
  RelativeExtensionEndpointWitness.iso_heq_of_dataEq
    (functorHomotopySourceCanonicalWitness H p s hi) w
    (functorHomotopySourceRestrictedWitness H p s hi w false)
    (functorHomotopySourceRestrictedWitness H p s hi w true)
    (functorHomotopySourceFamily_base_restrict H p s w)
    (functorHomotopySourceFamily_initial_restrict s)
    (functorHomotopySourceFamily_apex_restrict p) rfl rfl rfl rfl
    (prismEndpoint_zero_leftAnodyne C) w.initial_base
    (functorHomotopySourceRestrictedWitness H p s hi w true).initial_base w.endpoint_base
    (functorHomotopySourceRestrictedWitness H p s hi w true).endpoint_base

end SerrePositivity.InfinityCategories.F2
