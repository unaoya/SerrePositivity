module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorOverIsomorphism
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorFiberHom

/-!
概要：底上の全空間の同型による相対 Hom の移送は、同じ fiber の全 Hom 作用と可換。
方針：始域の逆同型と標的の順同型で共役する式を、全ての評価単体で照合する。
規約：充填性や同値性の仮定は不要。全パラメーターでの射の厳密な等式。
使われ方：小さい unstraightening の c1 比較を、大きい fiber の実際の輸送作用へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 全空間の底上の同型は、相対 Hom の全 fiber 作用を同じ fiber の同型で共役する。 -/
lemma relativeFunctorOverIso_fiberHom {B : SSet.{u}}
    {a a' p p' : Over B} (ea : a ≅ a') (ep : p ≅ p') (b : B _⦋0⦌) :
    (relativeFunctorOverIso ea ep).hom ≫ relativeFunctorFiberHom a'.hom p'.hom b =
    relativeFunctorFiberHom a.hom p.hom b ≫
      (pre (vertexFiberMap a'.hom a.hom ea.inv.left ea.inv.w b)).app (vertexFiber p.hom b) ≫
      (ihom (vertexFiber a'.hom b)).map
        (vertexFiberMap p.hom p'.hom ep.hom.left ep.hom.w b) := by
  rw [relativeFunctorOverIso_hom]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories
