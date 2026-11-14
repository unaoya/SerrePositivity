module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanFrameCofibrancy
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
概要：BK重みの単体パラメータ付き実現は単射をcofibrationへ送る。
方針：既存の重み付き切断随伴とframe実現随伴を合成し、持ち上げ性を直接移す。
規約：SSetの完全なモデル構造や、未証明の左Quillen性は使用しない。
使われ方：HTT 4.2.4.4のRR02(a)、実現による余単体的frameの境界条件。
-/

@[expose] public noncomputable section
universe w u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  (A : K ⥤ SimplexCategory ⥤ C)

/-- BK重みを左因子として固定した、実際のパラメータ付き実現。 -/
def bousfieldKanParameterRealization : SSet.{w} ⥤ C :=
  weightedParameterFunctor (bousfieldKanWeight Kᵒᵖ) ⋙ functor K A

/-- 既存の二随伴の合成。右辺は元のframe HomのBK end。 -/
def bousfieldKanParameterAdjunction :
    bousfieldKanParameterRealization K A ⊣
      hom K A ⋙ weightedSectionsFunctor (bousfieldKanWeight Kᵒᵖ) :=
  (weightedSectionsAdjunction (bousfieldKanWeight Kᵒᵖ)).comp (adjunction K A)

instance bousfieldKanParameterRealization_isLeftAdjoint :
    (bousfieldKanParameterRealization K A).IsLeftAdjoint :=
  (bousfieldKanParameterAdjunction K A).isLeftAdjoint

variable [ModelCategory C]
  (hA : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (A.obj k)))

include hA in
/-- 単射の実像は、元のCのモデル構造でcofibration。 -/
lemma bousfieldKanParameterRealization_map_cofibration {U V : SSet.{w}}
    (i : U ⟶ V) [Mono i] :
    cofibrations C ((bousfieldKanParameterRealization K A).map i) := by
  rw [← trivialFibrations_llp C]
  intro Y Z p hp
  have : Fibration p := ⟨hp.1⟩
  have : WeakEquivalence p := ⟨hp.2⟩
  have : ∀ k, TrivialKanFibration (((hom K A).map p).app k) := by
    intro k
    apply (trivialKanFibration_iff_boundary _).mpr
    intro n
    exact HomotopyFunctionComplex.boundary_lifting_of_reedyCofibrant
      (A.obj k.unop) n (hA k.unop) p
  apply ((bousfieldKanParameterAdjunction K A).hasLiftingProperty_iff i p).mpr
  exact (bousfieldKanMap_trivialKanFibration ((hom K A).map p)).mem i inferInstance

end SerrePositivity.DiagramModel.FrameWeightRealization
