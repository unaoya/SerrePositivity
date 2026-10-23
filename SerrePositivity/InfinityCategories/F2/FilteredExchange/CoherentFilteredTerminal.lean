module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FilteredLeftFibrationContractibility
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalColimit
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceTerminalValues

/-!
概要：一般 coherent filtered 図式の全ての値が終対象なら、元の余極限も終対象。
方針：元の値の可縮性から全空間 Kan 模型の可縮性を得て、終対象性へ戻す。
規約：元の図式・選んだ余錐を保持。使われ方：有限極限交換の空形状の段階。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (hf : ∀ b : B _⦋0⦌, IsTerminalVertex (F.app (Opposite.op ⦋0⦌) (ULift.up b)))
include hf

/-- 全ての値が終対象なら、元の全空間余極限の頂点は終対象。 -/
lemma coherentFilteredTotalVertex_isTerminal : IsTerminalVertex (coherentDiagramTotalVertex F) := by
  apply (HomotopyLimits.spaceInfinity_isTerminal_iff_value_isContractibleKan _).mpr
  rw [coherentDiagramTotalVertex_object]
  apply coherentFilteredTotalKan_isContractibleKan F
  intro b
  exact (HomotopyLimits.spaceInfinity_isTerminal_iff_value_isContractibleKan _).mp (hf b)

/-- 全ての値が終対象なら、任意の元の余極限余錐の頂点も終対象。 -/
lemma coherentFilteredColimitVertex_isTerminal (c : JoinCocone F) (hc : IsColimitCone c) :
    IsTerminalVertex c.vertex := by
  have ht : IsTerminalVertex (coherentDiagramTotalCocone F).vertex := by
    rw [coherentDiagramTotalCocone_vertex]
    exact coherentFilteredTotalVertex_isTerminal F hf
  exact ht.of_vertexIso
    (colimitVertexIso (coherentDiagramTotalCocone F) c (coherentDiagramTotalCocone_isColimit F) hc)

end SerrePositivity.InfinityCategories.F2
