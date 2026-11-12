module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanSpecifiedPathLift
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyPathReplacement
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeEquivalencePathExtension
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：指定ホモトピーで可換な射を、同じ底の射へ厳密に写る射に補正する。
方針：底の全可逆 path を指定した始点から持ち上げ、その終点を読む。
規約：指定ホモトピーを選び直さない。使われ方：持ち上げた実 fiber cospan の厳密化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B T : SSet.{u}} [KanComplex E] [KanComplex B]
  (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
  (a : T ⟶ E) (b : T ⟶ B) (H : SSet.Homotopy (a ≫ p) b)

/-- 元の全ホモトピーを指定始点から持ち上げた実際の可逆 path。 -/
def kanHomotopyRectificationPath : T ⟶ equivalencePath E :=
  HomotopyLimits.kanSpecifiedPathLift p 0 a (homotopyEquivalencePath H)
    (homotopyEquivalencePath_zero H)

/-- 底には元の指定ホモトピーの全 path がそのまま残る。 -/
lemma kanHomotopyRectificationPath_projection :
    kanHomotopyRectificationPath p a b H ≫ equivalencePathMap p = homotopyEquivalencePath H :=
  HomotopyLimits.kanSpecifiedPathLift_projection _ _ _ _ _

/-- 持ち上げの始点は元の射。 -/
lemma kanHomotopyRectificationPath_source :
    kanHomotopyRectificationPath p a b H ≫ equivalencePathEndpoint E 0 = a :=
  HomotopyLimits.kanSpecifiedPathLift_endpoint _ _ _ _ _

/-- 指定した底の射へ厳密に写る、元の射の補正。 -/
def kanHomotopyRectification : T ⟶ E :=
  kanHomotopyRectificationPath p a b H ≫ equivalencePathEndpoint E 1

/-- 補正後の射は指定した底の射に厳密に一致する。 -/
lemma kanHomotopyRectification_over : kanHomotopyRectification p a b H ≫ p = b := by
  change (kanHomotopyRectificationPath p a b H ≫ equivalencePathEndpoint E (0 : Fin 2).rev)
    ≫ p = b
  rw [kanHomotopyRectificationPath, HomotopyLimits.kanSpecifiedPathLift_other_endpoint]
  exact homotopyEquivalencePath_one H

/-- 同じ持ち上げの全可逆 path から、元の射と補正後の射の間の円柱を読む。 -/
def kanHomotopyRectificationHomotopy : SSet.Homotopy a (kanHomotopyRectification p a b H) where
  h := (kanHomotopyRectificationPath p a b H ▷ (Δ[1] : SSet.{u})) ≫
    (equivalencePathHomotopy E).h
  h₀ := by
    change _ = a
    rw [SSet.ι₀_comp_assoc, (equivalencePathHomotopy E).h₀]
    exact kanHomotopyRectificationPath_source p a b H
  h₁ := by
    change _ = kanHomotopyRectification p a b H
    rw [SSet.ι₁_comp_assoc, (equivalencePathHomotopy E).h₁]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 同じ指定持ち上げの全円柱の類を保持する、元の射から補正後の射への関手同型。 -/
def kanHomotopyRectificationIso : FunctorIso a (kanHomotopyRectification p a b H) :=
  functorIsoOfSimplicialHomotopy (kanHomotopyRectificationHomotopy p a b H)

/-- 元の射が同値なら、指定ホモトピーによる厳密化後も同値。 -/
lemma kanHomotopyRectification_homotopyEquivalence [KanComplex T]
    (ha : IsSimplicialHomotopyEquivalence a) :
    IsSimplicialHomotopyEquivalence (kanHomotopyRectification p a b H) :=
  (ha.isQCatEquivalence.ofFunctorIso
    (kanHomotopyRectificationIso p a b H)).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
