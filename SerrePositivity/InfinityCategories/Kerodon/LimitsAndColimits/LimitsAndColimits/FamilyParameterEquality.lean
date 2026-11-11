module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan

/-!
概要：内部 Hom の同じ高次単体を、元の全標準単体パラメーターの等号へ戻す。
方針：Yoneda の自然性と curry の単射性を使う。
規約：頂点に制限しない、任意の次数の等号。
使われ方：実 encoder の等号から同じ全パラメーターの二胞体族を比較する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

lemma curry_app_eq_parameter {A B X : SSet.{u}} (F : A ⊗ B ⟶ X)
    {n : ℕ} (p q : B _⦋n⦌)
    (h : (curry F).app (Opposite.op ⦋n⦌) p = (curry F).app (Opposite.op ⦋n⦌) q) :
    (A ◁ SSet.yonedaEquiv.symm p) ≫ F = (A ◁ SSet.yonedaEquiv.symm q) ≫ F := by
  apply curry_injective
  rw [curry_natural_left, curry_natural_left,
    SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, h]

lemma curry_app_eq_of_parameter_eq {A B X : SSet.{u}} (F : A ⊗ B ⟶ X)
    {n : ℕ} (p q : B _⦋n⦌)
    (h : (A ◁ SSet.yonedaEquiv.symm p) ≫ F = (A ◁ SSet.yonedaEquiv.symm q) ≫ F) :
    (curry F).app (Opposite.op ⦋n⦌) p = (curry F).app (Opposite.op ⦋n⦌) q := by
  apply (SSet.yonedaEquiv (n := ⦋n⦌)).symm.injective
  have hc := congrArg curry h
  rw [curry_natural_left, curry_natural_left,
    SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp] at hc
  exact hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
