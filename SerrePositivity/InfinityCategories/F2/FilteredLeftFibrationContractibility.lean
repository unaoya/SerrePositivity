module

public import SerrePositivity.InfinityCategories.F2.CoherentFilteredTotalDetection
public import SerrePositivity.InfinityCategories.Core.HomotopyBoundaryExtension
public import SerrePositivity.InfinityCategories.Core.EquivalenceTerminal

/-!
概要：filtered な底と可縮 fiber を持つ全空間の Kan 模型は可縮。
方針：各有限境界を一つの fiber で表し、その充填を実際のホモトピーで戻す。
規約：底の nerve 表示や coherent 余極限の存在を仮定しない。
使われ方：一般 coherent な filtered 図式の全空間模型での有限極限の検査。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：filtered な底で全 fiber が可縮なら、全空間の Kan 置換は可縮。
方針：境界を一つの fiber へ移し、そこでの充填をホモトピーで戻す。
規約：零次元も含めて全境界を充填する。使われ方：coherent 全空間模型の可縮性。 -/
lemma continuousKanLeftFibration_isContractibleKan {E B : SSet.{u}}
    [Quasicategory B] [IsFilteredInfinity B] (p : E ⟶ B) [LeftFibration p]
    (hf : ∀ b, IsContractibleKan (vertexFiber p b)) :
    IsContractibleKan (continuousKanReplacement.obj E) := by
  intro n f
  obtain ⟨b, g, ⟨H⟩⟩ := continuousKanLeftFibration_finite_fiber_detection_unreplaced p f
  obtain ⟨w, hw⟩ := hf b n g
  have h := (functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨H⟩
  obtain ⟨e⟩ := nonempty_vertexIso_of_piZero_eq h.symm
  apply (show FunctorIso
    (g ≫ vertexFiberι p b ≫ continuousKanReplacementUnit.app E) f from e).exists_boundaryFilling
  refine ⟨w ≫ vertexFiberι p b ≫ continuousKanReplacementUnit.app E, ?_⟩
  rw [← Category.assoc, ← Category.assoc, hw, Category.assoc]

/-- 概要：filtered な一般 coherent 図式の値が全て可縮なら全空間模型も可縮。
方針：元の値の可縮性を fiber 比較の逆同値で戻し、有限境界の検出を使う。
規約：余極限性を仮定せず候補模型自体の全境界を充填する。使われ方：一般図式の比較。 -/
lemma coherentFilteredTotalKan_isContractibleKan {B : SSet.{u}}
    [Quasicategory B] [IsFilteredInfinity B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (hf : ∀ b : B _⦋0⦌,
      IsContractibleKan (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up b))).obj) :
    IsContractibleKan (coherentDiagramTotalKan F) := by
  apply continuousKanLeftFibration_isContractibleKan (smallLeftUnstraighteningProjection F)
  intro b
  exact (smallLeftUnstraighteningFiberValueEquivalence F b).symm.isContractibleKan (hf b)

end SerrePositivity.InfinityCategories.F2
