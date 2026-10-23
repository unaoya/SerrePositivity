module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantUnstraighteningFiberMapOverPre
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleSourceValue

/-!
概要：定値標的の指定三角形を、任意の fiber 射と元の始点射で写した値の同定。
方針：元の相対比較の前合成と、任意の fiber 射への作用の可換性を使う。
規約：三角形・両射を保持。使われ方：固定 native 値への定値三角形の因子。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C X : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
  {z : SpaceInfinity.{u} _⦋0⦌}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G (SSet.const z)}
  {c : SSet.Homotopy F (SSet.const z)} (T : FunctorCompositionTriangle a b c)
  (s : C ⟶ leftUnstraightening F) (g : vertexFiber pointedSpaceProjection z ⟶ X)
local notation "p" => s ≫ leftUnstraighteningProjection F
local notation "pF" => leftUnstraighteningProjection F
local notation "pJ" => leftUnstraighteningProjection (SSet.const z : B ⟶ SpaceInfinity)
local notation "Q" => Iso.hom (constantUnstraighteningRelativeIso p z) ≫
  CategoryTheory.Functor.map (ihom C) g
local notation "QF" => Iso.hom (constantUnstraighteningRelativeIso pF z) ≫
  CategoryTheory.Functor.map (ihom (leftUnstraightening F)) g

/-- 元の指定三角形の全空間比較を、任意の同じ fiber 射へ写した値。 -/
def functorTriangleFiberActionIso :=
  FunctorIso.postcomp (unstraighteningTriangleVertexIso F G (SSet.const z)
    (coherentVertexOfHomotopy a) (coherentVertexOfHomotopy b) (coherentVertexOfHomotopy c)
    (coherentTriangleOfFunctorTriangle T).diagram (coherentTriangleOfFunctorTriangle T).first
    (coherentTriangleOfFunctorTriangle T).second (coherentTriangleOfFunctorTriangle T).long)
    (constantUnstraighteningFiberProjection B z ≫ g)

/-- 任意の始点の指定三角形成分を任意の fiber 射で写した値は、同じ実射の前合成。 -/
lemma functorTriangleSequentialPostComparison_source_fiberMap_heq :
    HEq (VertexIso.map ((functorTriangleSequentialPostComparison T p).app
      (relativeFunctorVertex pF p s rfl)) Q)
      ((functorTriangleFiberActionIso T g).precomp s) := by
  refine (functorTriangleSequentialPostComparison_source_app_map_heq T s Q).trans ?_
  refine (heq_of_eq (vertexIso_map_comp (functorTriangleRelativeComparison T)
    (relativeFunctorPre pJ pF s) Q)).trans ?_
  have hv : relativeFunctorPre pJ pF s ≫ Q = QF ≫ (pre s).app X :=
    constantUnstraighteningRelativeIso_fiberMap_overPre pF (s ≫ pF) s rfl z g
  refine (vertexIso_map_heq (functorTriangleRelativeComparison T) hv).trans ?_
  unfold functorTriangleFiberActionIso
  rw [functorIso_precomp_eq_mapIso, functorIso_postcomp_eq_mapIso]
  unfold unstraighteningTriangleVertexIso
  rw [constantUnstraighteningRelativeIso_fiberMap_eq_projection pF z g]
  change HEq (VertexIso.map (functorTriangleRelativeComparison T) _)
    (VertexIso.map (VertexIso.map (VertexIso.map (functorTriangleRelativeComparison T)
      (vertexFiberι ((ihom (leftUnstraightening F)).map pJ) (functorVertex pF)))
        ((ihom (leftUnstraightening F)).map
          (constantUnstraighteningFiberProjection B z ≫ g))) ((pre s).app X))
  rw [vertexIso_map_comp, vertexIso_map_comp]
  exact vertexIso_map_heq _ (Category.assoc _ _ _)

/-- 元の底上の始点等式を明示した表示でも、同じ fiber 射への値を保持する。 -/
lemma functorTriangleSequentialPostComparison_source_fiberMap_heq_over_base
    (d : C ⟶ B) (hd : s ≫ pF = d) :
    HEq (VertexIso.map ((functorTriangleSequentialPostComparison T d).app
      (relativeFunctorVertex pF d s hd))
      ((constantUnstraighteningRelativeIso d z).hom ≫ (ihom C).map g))
      ((functorTriangleFiberActionIso T g).precomp s) := by
  cases hd
  exact functorTriangleSequentialPostComparison_source_fiberMap_heq T s g

end SerrePositivity.InfinityCategories.F2
