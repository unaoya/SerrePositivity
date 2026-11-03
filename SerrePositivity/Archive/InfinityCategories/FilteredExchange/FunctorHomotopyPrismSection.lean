module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyPrismBase
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeUncurryPointVertices

/-!
概要：元の指定変換の普遍 prism を、全始域射が動く一つの相対関手空間の射へ束ねる。
方針：始域射の全空間の普遍評価へ元の同じ prism を前合成し、相対 curry する。
規約：元の選択済み作用を保持。使われ方：始点も動く prism 比較の自然性。
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
  (H : SSet.Homotopy F G) (p : C ⟶ B)
local notation "U" => relativeFunctorSpace (leftUnstraighteningProjection F) p
local notation "s" => relativeFunctorUncurry (𝟙 U)
local notation "d" => (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)

/-- 元の普遍 prism を、すべての始域射が動く同じ全族へ展開する。 -/
def functorHomotopyPrismSectionLift : ((Δ[1] : SSet.{u + 1}) ⊗ C) ⊗ U ⟶
    PointedSpaceInfinity.{u} :=
  (α_ Δ[1] C U).hom ≫ functorHomotopyPointedPrism H s

/-- 全始域射の普遍 prism は、元の同じ全底を被覆する。 -/
lemma functorHomotopyPrismSectionLift_projection :
    functorHomotopyPrismSectionLift H p ≫ pointedSpaceProjection = fst (Δ[1] ⊗ C) U ≫ d := by
  rw [functorHomotopyPrismSectionLift, Category.assoc,
    functorHomotopyPointedPrism_projection, relativeFunctorUncurry_projection]
  apply SSet.hom_ext
  intro n
  rfl

/-- 全始域射の普遍 prism は、すべての元の始域射を初期値として厳密に保持する。 -/
lemma functorHomotopyPrismSectionLift_source :
    (prismEndpoint 0 C ▷ U) ≫ functorHomotopyPrismSectionLift H p =
      s ≫ pullback.fst pointedSpaceProjection F := by
  rw [functorHomotopyPrismSectionLift, ← Category.assoc, prismEndpoint_associator]
  exact functorHomotopyPointedPrism_source H s

/-- 全始域射の普遍 prism の終点は、元の同じ選択済み作用の後合成。 -/
lemma functorHomotopyPrismSectionLift_target :
    (prismEndpoint 1 C ▷ U) ≫ functorHomotopyPrismSectionLift H p =
      s ≫ (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val ≫
        pullback.fst pointedSpaceProjection G := by
  rw [functorHomotopyPrismSectionLift, ← Category.assoc, prismEndpoint_associator]
  exact functorHomotopyPointedPrism_target H s

/-- 元の普遍 prism を、始点も動く全相対 prism 空間へ束ねる射。 -/
def functorHomotopyPrismSection : U ⟶ relativeFunctorSpace pointedSpaceProjection d :=
  relativeFunctorCurry (functorHomotopyPrismSectionLift H p)
    (functorHomotopyPrismSectionLift_projection H p)

/-- 同じ全族の展開は、元の全始域射の普遍 prism そのもの。 -/
lemma functorHomotopyPrismSection_uncurry :
    relativeFunctorUncurry (functorHomotopyPrismSection H p) =
      functorHomotopyPrismSectionLift H p :=
  relativeFunctorUncurry_curry _ _

end SerrePositivity.InfinityCategories.F2
