module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantUnstraighteningFiberMapOverPre
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSquareTotalComponentMap
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleTotalAction
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：定値標的の元の二面比較を、任意の同じ fiber 射の実作用へ値まで戻す。
方針：元の恒等初期値成分と全係数の fiber 射影表示を使う。
規約：共有対角・元の二面・値射を保持。使われ方：raw fiber 比較と native 中央比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B X : SSet.{u + 1}} {F G L : B ⟶ SpaceInfinity.{u}}
  {z : SpaceInfinity.{u} _⦋0⦌}
  {a : SSet.Homotopy F G} {v : SSet.Homotopy G (SSet.const z)}
  {d : SSet.Homotopy F (SSet.const z)} {s : SSet.Homotopy F L}
  {w : SSet.Homotopy L (SSet.const z)}
  (U : FunctorCompositionTriangle a v d) (D : FunctorCompositionTriangle s w d)
  (g : vertexFiber pointedSpaceProjection z ⟶ X)
local notation "p" => leftUnstraighteningProjection F
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "e" => Iso.symm (FunctorIso.app (functorTriangleSequentialPostComparison D p) x₀) ≪≫
  FunctorIso.app (functorTriangleSequentialPostComparison U p) x₀

/-- 定値標的の元の二面比較の像は、同じ全空間比較の同じ fiber 射への後合成。 -/
lemma functorSquareComparison_value_fiberMap :
    HEq (VertexIso.map e
      ((constantUnstraighteningRelativeIso p z).hom ≫ (ihom (leftUnstraightening F)).map g))
      (FunctorIso.postcomp
        ((functorTriangleTotalActionIso D).symm ≪≫ functorTriangleTotalActionIso U)
        (constantUnstraighteningFiberProjection B z ≫ g)) := by
  refine (functorSquareComparison_total_app_map_heq U D _).trans ?_
  rw [constantUnstraighteningRelativeIso_fiberMap_eq_projection,
    functorIso_postcomp_eq_mapIso, ← vertexIso_map_comp, vertexIso_map_trans, vertexIso_map_symm]
  rfl

end SerrePositivity.InfinityCategories.F2
