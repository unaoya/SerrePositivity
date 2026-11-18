module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.HoHomVertexTransport

/-!
概要：同じ全写像の表示の等式に沿う、端点を保つ Hom 移送の自然性。
方針：写像の等式を消去し、端点の等式の証明の一意性を用いる。
使われ方：Kerodon §1.4.5（Tag 0049）、HTT §1.2.3 の元の関手作用の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 端点が元の像そのものなら、移送は元の関手作用に等しい。 -/
lemma hoHomMapWithVertexEqualities_refl {A B : SSet.{u}} (f : A ⟶ B)
    {x y : A _⦋0⦌}
    (β : (SSet.HomotopyCategory.mk x : hoFunctor.obj A) ⟶ SSet.HomotopyCategory.mk y) :
    hoHomMapWithVertexEqualities f rfl rfl β = (hoFunctor.map f).toFunctor.map β := by
  simp only [hoHomMapWithVertexEqualities, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 元の全写像を等しい表示に変えても、指定した端点の Hom 移送は同じ。 -/
lemma hoHomMapWithVertexEqualities_congr {A B : SSet.{u}} {f g : A ⟶ B} (hfg : f = g)
    {x y : A _⦋0⦌} {x' y' : B _⦋0⦌}
    (hx : f.app (Opposite.op ⦋0⦌) x = x') (hy : f.app (Opposite.op ⦋0⦌) y = y')
    (hx' : g.app (Opposite.op ⦋0⦌) x = x') (hy' : g.app (Opposite.op ⦋0⦌) y = y')
    (β : (SSet.HomotopyCategory.mk x : hoFunctor.obj A) ⟶ SSet.HomotopyCategory.mk y) :
    hoHomMapWithVertexEqualities f hx hy β = hoHomMapWithVertexEqualities g hx' hy' β := by
  cases hfg
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
