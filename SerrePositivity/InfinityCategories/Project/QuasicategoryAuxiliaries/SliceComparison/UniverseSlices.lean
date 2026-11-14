module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseConeHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice

/-! # slice/coslice と宇宙持ち上げの可換性

概要：小さい図式の slice/coslice の ULift は、持ち上げた図式の slice/coslice と実同型。
方針：join からの全写像の全単射を固定図式の条件で制限し、全単体作用を照合する。
規約：図式や標的の quasicategory 性は不要。使われ方：極限・余極限の宇宙降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 実 slice の各次数は宇宙持ち上げの前後で全単射に対応する。 -/
def uliftSliceOverSimplexEquiv {K X : SSet.{u}} (p : K ⟶ X) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) _⦋n⦌ ≃ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.uliftFunctor.{v, u}).map p)) _⦋n⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeHomEquiv K X n).subtypeEquiv (by
    intro F
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) K ≫ F = p ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K) ≫
        ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso K n).inv ≫ (SSet.uliftFunctor.{v, u}).map F) =
          (SSet.uliftFunctor.{v, u}).map p
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso_inv_inr, ← Functor.map_comp]
    exact (SSet.uliftFunctor.{v, u}).map_injective.eq_iff.symm)

/-- 実 coslice の各次数も宇宙持ち上げの前後で全単射に対応する。 -/
def uliftSliceUnderSimplexEquiv {K X : SSet.{u}} (p : K ⟶ X) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) _⦋n⦌ ≃ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder ((SSet.uliftFunctor.{v, u}).map p)) _⦋n⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeHomEquiv K X n).subtypeEquiv (by
    intro F
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[n] : SSet.{u}) ≫ F = p ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((SSet.uliftFunctor.{v, u}).obj K) (Δ[n] : SSet.{max u v}) ≫
        ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso K n).inv ≫ (SSet.uliftFunctor.{v, u}).map F) =
          (SSet.uliftFunctor.{v, u}).map p
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso_inv_inl, ← Functor.map_comp]
    exact (SSet.uliftFunctor.{v, u}).map_injective.eq_iff.symm)

/-- 実 slice の ULift と持ち上げた図式の実 slice は単体的に同型。 -/
def uliftSliceOverIso {K X : SSet.{u}} (p : K ⟶ X) :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.uliftFunctor.{v, u}).map p) :=
  NatIso.ofComponents (fun n => Equiv.toIso
    (Equiv.ulift.trans (uliftSliceOverSimplexEquiv p n.unop.len))) (fun α => by
      apply ConcreteCategory.hom_ext
      intro s
      apply Subtype.ext
      exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeHomEquiv_precomp K X α.unop s.down.val)

/-- 実 coslice の ULift と持ち上げた図式の実 coslice も単体的に同型。 -/
def uliftSliceUnderIso {K X : SSet.{u}} (p : K ⟶ X) :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder ((SSet.uliftFunctor.{v, u}).map p) :=
  NatIso.ofComponents (fun n => Equiv.toIso
    (Equiv.ulift.trans (uliftSliceUnderSimplexEquiv p n.unop.len))) (fun α => by
      apply ConcreteCategory.hom_ext
      intro s
      apply Subtype.ext
      exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeHomEquiv_precomp K X α.unop s.down.val)

/-- slice の順宇宙同型の実写像への作用。 -/
lemma uliftSliceOverIso_hom_val {K X : SSet.{u}} (p : K ⟶ X) {n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) _⦋n⦌) :
    (((uliftSliceOverIso.{u, v} p).hom.app (Opposite.op ⦋n⦌)) (ULift.up c)).val =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso.{u, v} K n).inv ≫ (SSet.uliftFunctor.{v, u}).map c.val := rfl

/-- coslice の順宇宙同型の実写像への作用。 -/
lemma uliftSliceUnderIso_hom_val {K X : SSet.{u}} (p : K ⟶ X) {n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) _⦋n⦌) :
    (((uliftSliceUnderIso.{u, v} p).hom.app (Opposite.op ⦋n⦌)) (ULift.up c)).val =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso.{u, v} K n).inv ≫ (SSet.uliftFunctor.{v, u}).map c.val := rfl

/-- slice の逆宇宙同型は形状を戻した射の一意な原像を取る。 -/
lemma uliftSliceOverIso_inv_val {K X : SSet.{u}} (p : K ⟶ X) {n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.uliftFunctor.{v, u}).map p)) _⦋n⦌) :
    (((uliftSliceOverIso.{u, v} p).inv.app (Opposite.op ⦋n⦌)) c).down.val =
      (SSet.uliftFunctor.{v, u}).preimage ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso.{u, v} K n).hom ≫ c.val) := rfl

/-- coslice の逆宇宙同型も形状を戻した射の一意な原像を取る。 -/
lemma uliftSliceUnderIso_inv_val {K X : SSet.{u}} (p : K ⟶ X) {n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder ((SSet.uliftFunctor.{v, u}).map p)) _⦋n⦌) :
    (((uliftSliceUnderIso.{u, v} p).inv.app (Opposite.op ⦋n⦌)) c).down.val =
      (SSet.uliftFunctor.{v, u}).preimage ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso.{u, v} K n).hom ≫ c.val) := rfl

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
