module
public import SerrePositivity.KST.Fibration.WeakMarkedSpanCartesianLift
public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanFamilyCocartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange

/-! # 全辺が元の W 分母に写る底図式上の span 族の両側 fibration 性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)

include h in
lemma weakSpanDenominatorBaseChange_cartesianFibration
    (x : B.obj _⦋0⦌) {T : SSet.{u}} (f : T ⟶ B.obj)
    (hW : ∀ e : T _⦋1⦌, f.app (Opposite.op ⦋1⦌) e ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration (pullback.snd
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x) f) := by
  let π := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x
  refine ⟨innerFibrations.pullback_snd π f (InnerFibration.mem (q := π)), ?_⟩
  intro v e he
  change stdSimplex.δ (0 : Fin 2) ≫ e =
    SSet.yonedaEquiv.symm ((pullback.snd π f).app (Opposite.op ⦋0⦌) v) at he
  let w := (pullback.fst π f).app (Opposite.op ⦋0⦌) v
  have hb : stdSimplex.δ (0 : Fin 2) ≫ (e ≫ f) =
      SSet.yonedaEquiv.symm (π.app (Opposite.op ⦋0⦌) w) := by
    rw [← Category.assoc, he]
    have hcond := congrArg (fun k => k.app (Opposite.op ⦋0⦌) v)
      (pullback.condition (f := π) (g := f))
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
      NatTrans.comp_app_apply, w] using hcond.symm
  have ht : B.obj.δ 0 (SSet.yonedaEquiv (e ≫ f)) =
      π.app (Opposite.op ⦋0⦌) w := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hb, Equiv.apply_symm_apply]
  let s : Truncated.Edge (X := (truncation 2).obj B.obj)
      (B.obj.δ 1 (SSet.yonedaEquiv (e ≫ f)))
      (π.app (Opposite.op ⦋0⦌) w) := ⟨SSet.yonedaEquiv (e ≫ f), rfl, ht⟩
  have hs : s.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
    dsimp only [s]
    rw [SSet.yonedaEquiv_comp]
    exact hW _
  obtain ⟨G, hG, hGπ, hGc⟩ := exists_weakMarkedSpanCartesianLift h x w s hs
  have hGf : G ≫ π = e ≫ f := hGπ.trans (SSet.yonedaEquiv.symm_apply_apply _)
  refine ⟨pullback.lift G e hGf, ?_, pullback.lift_snd _ _ _, ?_⟩
  · apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst, SSet.yonedaEquiv_symm_comp] using hG
    · simpa only [Category.assoc, pullback.lift_snd, SSet.yonedaEquiv_symm_comp] using he
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_pullback
    rw [← SSet.yonedaEquiv_comp, pullback.lift_fst]
    exact hGc

lemma weakSpanBaseChange_cocartesianFibration
    (x : B.obj _⦋0⦌) {T : SSet.{u}} (f : T ⟶ B.obj) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (pullback.snd
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x) f) :=
  inferInstance

end SerrePositivity.KST.Fibration
