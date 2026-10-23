module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningFiber
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ContinuousKanWeakFunctoriality
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedEmptyProductNative

/-!
概要：定値一点 coherent 図式の元の小さい全空間を、元の底へ比較する。
方針：元の fiber 値同値から可縮性を回収し、任意の底上の fiberwise 判定を使う。
規約：射は元の小さい unstraightening の射影。底の充填性は不要。
使われ方：sifted 余極限の空積保存を元の coherent 余極限頂点へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 定値一点図式の元の小さい全空間の射影は、任意の底上で前合成同値。 -/
lemma coherentPointTotalProjection_isPrecompositionEquivalence (B : SSet.{u}) :
    IsPrecompositionEquivalence (smallLeftUnstraighteningProjection
      (SSet.const pointSpaceVertex.{u} : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _)) := by
  let F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u} :=
    SSet.const pointSpaceVertex
  let p := smallLeftUnstraighteningProjection F
  apply isPrecompositionEquivalence_of_leftFibration_fibers p (𝟙 B) p
    (Category.comp_id p)
  intro b
  have hpt : IsContractibleKan pointKanObject.{u}.obj := by
    intro n a
    exact ⟨stdSimplex.isTerminalObj₀.from _, stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  have hv : IsContractibleKan (spaceInfinityObject
      (F.app (Opposite.op ⦋0⦌) (ULift.up b))).obj := by
    change IsContractibleKan (spaceInfinityObject (spaceInfinityVertex pointKanObject)).obj
    exact hpt
  have hp := (smallLeftUnstraighteningFiberValueEquivalence F b).symm.isContractibleKan hv
  have hi := vertexFiber_isContractibleKan (𝟙 B) b
  have hc : IsWeakHomotopyEquivalence (vertexFiberMap p (𝟙 B) p (Category.comp_id p) b ≫
      terminal.from (vertexFiber (𝟙 B) b)) := by
    rw [show vertexFiberMap p (𝟙 B) p (Category.comp_id p) b ≫
      terminal.from (vertexFiber (𝟙 B) b) = terminal.from (vertexFiber p b) from
        terminal.hom_ext _ _]
    exact hp.isWeaklyContractible
  exact (hi.isWeaklyContractible.cancel_right hc).isSimplicialHomotopyEquivalence.isQCatEquivalence

/-- 同じ元の射影を Kan 置換した比較は、元の coherent 全空間模型から底の模型への同値。 -/
lemma coherentPointTotalKanProjection_isSimplicialHomotopyEquivalence (B : SSet.{u}) :
    IsSimplicialHomotopyEquivalence (F2.continuousKanReplacement.map
      (smallLeftUnstraighteningProjection
        (SSet.const pointSpaceVertex.{u} : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _))) :=
  (F2.continuousKanReplacement_map_isWeakHomotopyEquivalence _
    (coherentPointTotalProjection_isPrecompositionEquivalence B).isWeakHomotopyEquivalence
    ).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
