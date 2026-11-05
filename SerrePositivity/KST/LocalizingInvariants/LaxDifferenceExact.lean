module

public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceFunctor
public import SerrePositivity.KST.LocalizingInvariants.CofiberRotationExact

/-!
概要：元の lax pullback の差の実 ∞ 関手は完全。
方針：元の矢印射影の両端の完全性を F2 から取り、cofiber 回転の完全性へ渡す。
規約：元の全単体上の関手を ExactMap に束ねる。使われ方：差の Verdier 列と値の fiber 列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {C D E : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)

lemma laxArrow_isExact : IsExactFunctor (F2.laxPullbackArrow p.hom q.hom) := by
  have : IsExactFunctor (F2.laxPullbackArrow p.hom q.hom ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
    rw [F2.laxPullbackArrow_source]
    infer_instance
  have : IsExactFunctor (F2.laxPullbackArrow p.hom q.hom ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [F2.laxPullbackArrow_target]
    infer_instance
  exact arrow_exact_of_endpoints E.obj _

instance laxDifference_isExact : IsExactFunctor (laxDifference p q) := by
  have := laxArrow_isExact p q
  exact CofiberFamily.cofiber_isExact E.obj (F2.laxPullbackArrow p.hom q.hom)

/-- 元の差の関手を完全関手に束ねる。 -/
def exactLaxDifference : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) E := ⟨laxDifference p q, inferInstance⟩

lemma exactLaxDifference_kernel (x : (laxCategory p q).obj _⦋0⦌) :
    IsZeroVertex ((exactLaxDifference p q).hom.app (Opposite.op ⦋0⦌) x) ↔
      x ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.essentialImage (pullbackInclusion p q) := laxDifference_kernel p q x

end SerrePositivity.KST.LocalizingInvariants
