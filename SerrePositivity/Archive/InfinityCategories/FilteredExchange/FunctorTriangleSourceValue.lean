module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleSourceComponentMap
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleConstantTargetValue
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantUnstraighteningValueOverPre

/-!
概要：定値標的の指定三角形の任意の始点成分を、同じ実射の前合成として値へ写す。
方針：元の相対始点成分を回収し、値への作用と相対前合成の厳密な自然性を使う。
規約：指定比較も始点射も保持。使われ方：元の定値余極限三角形の単位での評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
  {z : SpaceInfinity.{u} _⦋0⦌}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G (SSet.const z)}
  {c : SSet.Homotopy F (SSet.const z)} (T : FunctorCompositionTriangle a b c)
  (s : C ⟶ leftUnstraightening F)
local notation "p" => s ≫ leftUnstraighteningProjection F
local notation "pF" => leftUnstraighteningProjection F
local notation "pJ" => leftUnstraighteningProjection (SSet.const z : B ⟶ SpaceInfinity)
local notation "Q" => Iso.hom (constantUnstraighteningRelativeIso p z) ≫
  CategoryTheory.Functor.map (ihom C) (QCatEquivalence.hom (pointedSpaceFiberValueEquivalence z))
local notation "QF" => Iso.hom (constantUnstraighteningRelativeIso pF z) ≫
  CategoryTheory.Functor.map (ihom (leftUnstraightening F))
    (QCatEquivalence.hom (pointedSpaceFiberValueEquivalence z))
local notation "W" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (KanObject.obj (spaceInfinityObject z))

/-- 元の任意始点での指定三角形成分の値は、同じ全空間三角形比較の前合成そのもの。 -/
lemma functorTriangleSequentialPostComparison_source_value_heq :
    HEq (VertexIso.map ((functorTriangleSequentialPostComparison T p).app
      (relativeFunctorVertex pF p s rfl)) Q)
      ((functorTriangleConstantTargetActionIso T).precomp s) := by
  refine (functorTriangleSequentialPostComparison_source_app_map_heq T s Q).trans ?_
  refine (heq_of_eq (vertexIso_map_comp (functorTriangleRelativeComparison T)
    (relativeFunctorPre pJ pF s) Q)).trans ?_
  have hv : relativeFunctorPre pJ pF s ≫ Q = QF ≫ (pre s).app W :=
    constantUnstraighteningRelativeIso_value_overPre pF (s ≫ pF) s rfl z
  refine (vertexIso_map_heq (functorTriangleRelativeComparison T) hv).trans ?_
  unfold functorTriangleConstantTargetActionIso
  rw [functorIso_precomp_eq_mapIso, functorIso_postcomp_eq_mapIso]
  unfold unstraighteningTriangleVertexIso
  rw [constantUnstraighteningRelativeIso_value_eq_projection pF z]
  change HEq (VertexIso.map (functorTriangleRelativeComparison T) _)
    (VertexIso.map (VertexIso.map (VertexIso.map (functorTriangleRelativeComparison T)
      (vertexFiberι ((ihom (leftUnstraightening F)).map pJ) (functorVertex pF)))
        ((ihom (leftUnstraightening F)).map
          (constantUnstraighteningFiberProjection B z ≫
            (pointedSpaceFiberValueEquivalence z).hom))) ((pre s).app W))
  rw [vertexIso_map_comp, vertexIso_map_comp]
  exact vertexIso_map_heq _ (Category.assoc _ _ _)

/-- 底上の元の始点射の等式を保った表示でも、同じ指定値の前合成を回収する。 -/
lemma functorTriangleSequentialPostComparison_source_value_heq_over_base
    (d : C ⟶ B) (hd : s ≫ pF = d) :
    HEq (VertexIso.map ((functorTriangleSequentialPostComparison T d).app
      (relativeFunctorVertex pF d s hd))
      ((constantUnstraighteningRelativeIso d z).hom ≫
        (ihom C).map (pointedSpaceFiberValueEquivalence z).hom))
      ((functorTriangleConstantTargetActionIso T).precomp s) := by
  cases hd
  exact functorTriangleSequentialPostComparison_source_value_heq T s

end SerrePositivity.InfinityCategories.F2
