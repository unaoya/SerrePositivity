module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantUnstraighteningFiberMapPost
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSquareTotalComponentMap
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleTotalAction
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：元の二面比較の定値後合成の像を、同じ全空間二面比較の実後合成へ戻す。
方針：元の恒等初期値成分を回収し、任意の fiber 射への全作用を計算する。
規約：共有対角・二面・実射を保持。使われ方：五因子式の最初辺の後合成因子。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B X : SSet.{u + 1}} {F G L J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {v : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  {s : SSet.Homotopy F L} {w : SSet.Homotopy L J}
  (U : FunctorCompositionTriangle a v d) (D : FunctorCompositionTriangle s w d)
  {z : SpaceInfinity.{u} _⦋0⦌} (H : SSet.Homotopy J (SSet.const z))
  (g : vertexFiber pointedSpaceProjection z ⟶ X)
local notation "p" => leftUnstraighteningProjection F
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "e" => Iso.symm (FunctorIso.app (functorTriangleSequentialPostComparison D p) x₀) ≪≫
  FunctorIso.app (functorTriangleSequentialPostComparison U p) x₀
local notation "Q" => Iso.hom (constantUnstraighteningRelativeIso p z) ≫
  CategoryTheory.Functor.map (ihom (leftUnstraightening F)) g
local notation "f" => leftUnstraighteningMappingVertexMap J (SSet.const z)
  (coherentVertexOfHomotopy H)

/-- 定値後合成の元の二面比較成分は、同じ全空間二面比較の同じ実後合成の値。 -/
lemma functorSquareComparison_map_constantPost_fiberMap :
    HEq (VertexIso.map (VertexIso.map e (functorHomotopyRelativePost H p)) Q)
      (FunctorIso.postcomp
        ((functorTriangleTotalActionIso D).symm ≪≫ functorTriangleTotalActionIso U)
        ((Subtype.val f) ≫ constantUnstraighteningFiberProjection B z ≫ g)) := by
  refine (heq_of_eq (vertexIso_map_comp e (functorHomotopyRelativePost H p) Q)).trans ?_
  refine (functorSquareComparison_total_app_map_heq U D
    (functorHomotopyRelativePost H p ≫ Q)).trans ?_
  refine (vertexIso_map_heq ((functorTriangleRelativeComparison D).symm ≪≫
    functorTriangleRelativeComparison U)
    (constantUnstraighteningRelativeIso_fiberMap_post (leftUnstraighteningProjection J)
      p z (Subtype.val f) (Subtype.property f) g)).trans ?_
  rw [functorIso_postcomp_eq_mapIso, ← vertexIso_map_comp,
    vertexIso_map_trans, vertexIso_map_symm]
  rfl

end SerrePositivity.InfinityCategories.F2
