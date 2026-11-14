module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategories

/-! # 元の安定対象の等号に沿う、完全射と全自然同値の対象座標の輸送 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の安定対象の等号により、同じ完全射の対象座標だけを輸送する。 -/
def exactMapTransport {A B A' B' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (hA : A = A') (hB : B = B') (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A' B' := hA ▸ hB ▸ f

/-- 対象座標の輸送は、同じ元の完全射との異種等号を保持する。 -/
theorem exactMapTransport_heq {A B A' B' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (hA : A = A') (hB : B = B') (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    HEq (exactMapTransport hA hB f) f := by cases hA; cases hB; rfl

/-- 全関手同型を、同じ対象座標の等号に沿って全単体ごと輸送する。 -/
def exactMapTransportFunctorIso {A B A' B' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (hA : A = A') (hB : B = B') {f g : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f.hom g.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (exactMapTransport hA hB f).hom (exactMapTransport hA hB g).hom := by
  cases hA
  cases hB
  exact e

/-- 元の全頂点の零値条件は、同じ対象座標の輸送でも保たれる。 -/
theorem exactMapTransport_zero {A B A' B' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (hA : A = A') (hB : B = B') (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hf : ∀ x, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (f.hom.app (Opposite.op ⦋0⦌) x)) :
    ∀ x, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((exactMapTransport hA hB f).hom.app (Opposite.op ⦋0⦌) x) := by
  cases hA
  cases hB
  exact hf

end SerrePositivity.KST.Fibration
