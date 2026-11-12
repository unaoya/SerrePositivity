module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorInitial
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.HomotopyBoundaryExtension
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroDiagramComparison

/-!
概要：零値関手から出る辺と零値関手へ入る辺を、全単体の矢印族にする。
方針：関手 ∞ 圏の始対象・終対象から実ホモトピーを選び、prism を curry する。
規約：頂点ごとの辺の選択に弱めない。使われ方：K-8 の lax pullback の両包含。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.ZeroArrowFamily

variable {K X : SSet.{u}} {F G : K ⟶ X}

def ofHomotopy (H : SSet.Homotopy F G) : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h)

lemma ofHomotopy_source (H : SSet.Homotopy F G) : ofHomotopy H ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = F := by
  rw [ofHomotopy, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding]
  exact H.h₀

lemma ofHomotopy_target (H : SSet.Homotopy F G) : ofHomotopy H ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = G := by
  rw [ofHomotopy, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding]
  exact H.h₁

variable [Quasicategory X]

/-- 零値の始点から任意の関手への、実関手圏内のホモトピー。 -/
def fromZero (F G : K ⟶ X) (hF : ∀ k, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) k)) :
    SSet.Homotopy F G := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_functorVertex_of_pointwise F (fun k => (hF k).1)
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (h.isInitialHo.to (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)))

/-- 任意の関手から零値の終点への、実関手圏内のホモトピー。 -/
def toZero (F G : K ⟶ X) (hG : ∀ k, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (G.app (Opposite.op ⦋0⦌) k)) :
    SSet.Homotopy F G := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise G (fun k => (hG k).2)
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (h.isTerminalHo.from (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)))

end SerrePositivity.KST.LocalizingInvariants.ZeroArrowFamily
