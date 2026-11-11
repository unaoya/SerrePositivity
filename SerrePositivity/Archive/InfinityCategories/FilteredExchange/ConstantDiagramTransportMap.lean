module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ConstantDiagramTransportCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantUnstraighteningEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantDiagramTransportComparison

/-!
概要：元の実輸送の全関手族の両端を、元の実相対射の定値 fiber 表示に同定する。
方針：同じ実終点の等式を uncurry して fiber の包含後で比較する。
規約：元の輸送と元の実射を保持。使われ方：三角形比較の各点評価の両端。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の証拠の実輸送の全関手族は、元の実相対射の curry の定値 fiber 像。 -/
lemma constantDiagramTransportWitness_map {B K : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} {a : K ⟶ intervalMappingSpace x y}
    {g : leftUnstraightening (SSet.const x : B ⟶ _) ⊗ K ⟶
      leftUnstraightening (SSet.const y : B ⟶ _)}
    (hg : g ≫ leftUnstraighteningProjection (SSet.const y) =
      fst (leftUnstraightening (SSet.const x : B ⟶ _)) K ≫
        leftUnstraighteningProjection (SSet.const x))
    (w : UnstraighteningFamilyWitness (SSet.const x) (SSet.const y)
      (constantDiagramTransformation B a) g) :
    (constantDiagramTransportWitness w).map = relativeFunctorCurry g hg ≫
      (constantUnstraighteningRelativeIso
        (leftUnstraighteningProjection (SSet.const x : B ⟶ _)) y).hom := by
  apply uncurry_injective
  apply vertexFiber_hom_ext pointedSpaceProjection y
  rw [FiberTransportFamily.map, uncurry_curry, constantDiagramTransportWitness_endpoint,
    Category.assoc, constantUnstraighteningFiberProjection_ι,
    constantUnstraighteningRelativeIso_uncurry, relativeFunctorUncurry_curry]

/-- 元の相対関手族を実現する同じ輸送の全関手族は、その元の定値 fiber 像。 -/
lemma constantDiagramTransportWitness_map_of_uncurry {B K : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} {a : K ⟶ intervalMappingSpace x y}
    (m : K ⟶ relativeFunctorSpace
      (leftUnstraighteningProjection (SSet.const y : B ⟶ SpaceInfinity))
      (leftUnstraighteningProjection (SSet.const x : B ⟶ SpaceInfinity)))
    (w : UnstraighteningFamilyWitness (SSet.const x) (SSet.const y)
      (constantDiagramTransformation B a) (relativeFunctorUncurry m)) :
    (constantDiagramTransportWitness w).map = m ≫
      (constantUnstraighteningRelativeIso
        (leftUnstraighteningProjection (SSet.const x : B ⟶ _)) y).hom := by
  have h := constantDiagramTransportWitness_map (relativeFunctorUncurry_projection m) w
  have hm : relativeFunctorCurry (relativeFunctorUncurry m)
      (relativeFunctorUncurry_projection m) = m := by
    apply relativeFunctorUncurry_injective
    exact relativeFunctorUncurry_curry _ _
  rw [hm] at h
  exact h

/-- 元の定値図式輸送比較の始域は、同じ普遍実輸送の終点そのもの。 -/
lemma constantDiagramMappingTransportIso_source {B K : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} (a : K ⟶ intervalMappingSpace x y) :
    uncurry ((constantDiagramTransformation B a ≫
      leftUnstraighteningMappingSpaceMap (SSet.const x : B ⟶ SpaceInfinity) (SSet.const y)) ≫
        (constantUnstraighteningRelativeIso
          (leftUnstraighteningProjection (SSet.const x : B ⟶ _)) y).hom) =
      (constantDiagramTransportWitness (constantDiagramMappingFamilyWitness B a)).endpoint := by
  have h := constantDiagramTransportWitness_map_of_uncurry
    (constantDiagramTransformation B a ≫
      leftUnstraighteningMappingSpaceMap (SSet.const x : B ⟶ SpaceInfinity) (SSet.const y))
    (constantDiagramMappingFamilyWitness B a)
  simpa only [FiberTransportFamily.map, uncurry_curry] using congrArg uncurry h.symm

end SerrePositivity.InfinityCategories.F2
