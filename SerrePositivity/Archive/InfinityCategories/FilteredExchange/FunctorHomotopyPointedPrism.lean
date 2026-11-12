module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentHomotopyParameterizedPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningConstantFamilyMap
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.UnstraighteningMappingTrianglePrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PrismExtensionRestriction

/-!
概要：元の指定変換の普遍 pointed prism を、任意の実始域射で制限して保持する。
方針：既存の同じ実現証拠へ一点パラメータを代入し、両端と底を回収する。
規約：元の prism と選択済み作用を保持。使われ方：長辺の三証拠の最初の証拠。
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
  (H : SSet.Homotopy F G)

/-- 元の指定変換への一点パラメータの、元の選択済み普遍 pointed 証拠。 -/
def functorHomotopyPointedWitness :=
  unstraighteningMappingFamilyWitness F G
    (SSet.const (coherentVertexOfHomotopy H) : (Δ[0] : SSet.{u + 1}) ⟶ _)

variable (s : C ⟶ leftUnstraightening F)

/-- 元の普遍 pointed prism を同じ実始域射でそのまま制限する。 -/
def functorHomotopyPointedPrism : (Δ[1] : SSet.{u + 1}) ⊗ C ⟶ PointedSpaceInfinity.{u} :=
  prismParameterRestriction (lift s (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫
    (functorHomotopyPointedWitness H).prism

/-- 元の普遍 prism の制限の始点は、同じ元の実始域射の pointed 成分そのもの。 -/
lemma functorHomotopyPointedPrism_source :
    prismEndpoint 0 C ≫ functorHomotopyPointedPrism H s =
      s ≫ pullback.fst pointedSpaceProjection F := by
  change lift s (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫
    (prismEndpoint 0 (leftUnstraightening F) ▷ (Δ[0] : SSet.{u + 1})) ≫
      (functorHomotopyPointedWitness H).prism = _
  rw [(functorHomotopyPointedWitness H).source, ← Category.assoc, lift_fst]

/-- 元の普遍 prism の実終点は、同じ元の実始域射の後の選択済み作用そのもの。 -/
lemma functorHomotopyPointedPrism_target :
    prismEndpoint 1 C ≫ functorHomotopyPointedPrism H s =
      s ≫ (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val ≫
        pullback.fst pointedSpaceProjection G := by
  change lift s (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫
    (prismEndpoint 1 (leftUnstraightening F) ▷ (Δ[0] : SSet.{u + 1})) ≫
      (functorHomotopyPointedWitness H).prism = _
  rw [(functorHomotopyPointedWitness H).target, unstraighteningMappingConst_uncurry]
  simp only [Category.assoc, lift_fst_assoc]

/-- 元の普遍 prism の制限は、同じ指定円柱を元の実始域射の底で引き戻す。 -/
lemma functorHomotopyPointedPrism_projection :
    functorHomotopyPointedPrism H s ≫ pointedSpaceProjection =
      (Δ[1] ◁ (s ≫ leftUnstraighteningProjection F)) ≫ functorSimplexDiagram (curry H.h) := by
  rw [functorHomotopyPointedPrism, Category.assoc,
    (functorHomotopyPointedWitness H).projection, coherentVertexOfHomotopy_parameterizedPrism]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.F2
