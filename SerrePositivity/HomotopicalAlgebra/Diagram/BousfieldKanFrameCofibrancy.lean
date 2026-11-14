module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanWeightCofibrancy
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightRealization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryTensor

/-!
概要：指定BK重みのframe実現のcofibrancy。
方針：複体側の自明fibrationをcosimplicial Homへ移し、実重みの持ち上げを随伴で戻す。
規約：SSetのモデル構造は仮定しない。値のframeのReedy cofibrancyだけを使う。
使われ方：HTT 4.2.4.4のRR02(a)、指定free frame実現のcofibrancyへの接続。
-/

@[expose] public noncomputable section
universe w u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C] [ModelCategory C]
  (A : K ⥤ SimplexCategory ⥤ C)
  (hA : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (A.obj k)))

include hA in
/-- 指定BK重みの実現は、SSetのモデル構造なしにcofibrant。 -/
lemma bousfieldKanRealization_isCofibrant :
    IsCofibrant ((functor K A).obj (bousfieldKanWeight Kᵒᵖ)) := by
  constructor
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
  constructor
  intro a b sq
  obtain ⟨l, hl⟩ := exists_bousfieldKanWeight_lift ((hom K A).map p)
    ((adjunction K A).homEquiv _ _ b)
  refine CommSq.HasLift.mk' {
    l := ((adjunction K A).homEquiv _ _).symm l
    fac_left := initial.hom_ext _ _
    fac_right := ?_ }
  apply ((adjunction K A).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact hl

end SerrePositivity.DiagramModel.FrameWeightRealization
