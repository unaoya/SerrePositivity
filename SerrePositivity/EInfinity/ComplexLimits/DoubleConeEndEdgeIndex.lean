module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeOverNaturality

/-!
概要：元の二重 cone の先端と終端を結ぶ実辺を、同じ恒等射の通常単体へ同定する。
方針：終端成分の実 augmentation を回収し、先端の恒等射を全一単体の等式へ戻す。
規約：対象と実辺全体の厳密な一致。使われ方：slice 内の最初の頂点の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def doubleConeEndEdgeOrderHom (n : ℕ) : Fin 2 →o Fin (n + 3) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom (OrderHom.const _ (0 : Fin (n + 2)))

lemma doubleConeEndEdgeOrderHom_zero (n : ℕ) :
    doubleConeEndEdgeOrderHom n 0 = (0 : Fin (n + 2)).castSucc := rfl
lemma doubleConeEndEdgeOrderHom_one (n : ℕ) :
    doubleConeEndEdgeOrderHom n 1 = Fin.last (n + 2) := rfl
lemma doubleConeEndEdgeOrderHom_injective (n : ℕ) :
    Function.Injective (doubleConeEndEdgeOrderHom n) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [doubleConeEndEdgeOrderHom_zero,
    doubleConeEndEdgeOrderHom_one]

end SerrePositivity.EInfinity.ComplexLimits
