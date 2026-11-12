module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerFiber

/-!
概要：一方の射が inner fibration の通常の引き戻しの quasicategory 性。
方針：引き戻した inner fibration の始域のホーンを充填する。
規約：基底自体の quasicategory 性は要求しない。
使われ方：Kerodon §4.5.3（Tag 032Y） の同値の引き戻しの比較。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：右側の射が inner fibration なら左の quasicategory との引き戻しは quasicategory。
方針：第一射影が inner fibration であることを使う。
規約：左の始域だけに quasicategory 性を要求する。
使われ方：Kerodon §4.5.3（Tag 032Y） の通常の引き戻し。 -/
instance (priority := 100) quasicategory_pullback_of_innerFibration_right
    {E F B : SSet.{u}} (e : E ⟶ B) (p : F ⟶ B) [Quasicategory E] [InnerFibration p] :
    Quasicategory (pullback e p) := by
  have : InnerFibration (pullback.fst e p) :=
    ⟨innerFibrations.pullback_fst e p (InnerFibration.mem (q := p))⟩
  exact quasicategory_of_innerFibration (pullback.fst e p)

/-- 概要：左側の射が inner fibration なら右の quasicategory との引き戻しは quasicategory。
方針：第二射影が inner fibration であることを使う。
規約：右の始域だけに quasicategory 性を要求する。
使われ方：Kerodon §4.5.3（Tag 032Y） の通常の引き戻し。 -/
instance (priority := 100) quasicategory_pullback_of_innerFibration_left
    {E F B : SSet.{u}} (e : E ⟶ B) (p : F ⟶ B) [Quasicategory F] [InnerFibration e] :
    Quasicategory (pullback e p) := by
  have : InnerFibration (pullback.snd e p) :=
    ⟨innerFibrations.pullback_snd e p (InnerFibration.mem (q := e))⟩
  exact quasicategory_of_innerFibration (pullback.snd e p)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
