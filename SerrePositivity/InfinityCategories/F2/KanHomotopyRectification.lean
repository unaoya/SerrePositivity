module

public import SerrePositivity.InfinityCategories.HomotopyLimits.KanSpecifiedPathLift
public import SerrePositivity.InfinityCategories.F1B.HomotopyPathReplacement
public import SerrePositivity.InfinityCategories.F1B.KanRelativeEquivalencePathExtension
public import SerrePositivity.InfinityCategories.F2.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus

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
open CategoryTheory SSet
open SSet.modelCategoryQuillen
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

/-- 同じ指定持ち上げから得られる、元の射から補正後の射への関手同型。 -/
def kanHomotopyRectificationIso : FunctorIso a (kanHomotopyRectification p a b H) :=
  functorIsoOfEq (F1B.kanEquivalencePath_functorIso (kanHomotopyRectificationPath p a b H))
    (kanHomotopyRectificationPath_source p a b H) rfl

/-- 元の射が同値なら、指定ホモトピーによる厳密化後も同値。 -/
lemma kanHomotopyRectification_homotopyEquivalence [KanComplex T]
    (ha : IsSimplicialHomotopyEquivalence a) :
    IsSimplicialHomotopyEquivalence (kanHomotopyRectification p a b H) :=
  (ha.isQCatEquivalence.ofFunctorIso
    (kanHomotopyRectificationIso p a b H)).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
