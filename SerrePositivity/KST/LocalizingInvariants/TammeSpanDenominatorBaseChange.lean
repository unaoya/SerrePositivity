module

public import SerrePositivity.KST.LocalizingInvariants.TammeMarkedSpanCartesianLift
public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanFamilyCocartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange

/-!
概要：全辺が Tamme 分母へ写る任意の底図式上では、span の射影は両側 fibration。
方針：指定終点の実 cartesian lift を引き戻しの普遍性で組み合わせる。
規約：底図式に quasicategory 性を要求しない。使われ方：分母上の輸送と亜群化の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

lemma tammeSpanDenominatorBaseChange_cartesianFibration
    (x : (laxCategory p q).obj _⦋0⦌) {B : SSet.{u}} (f : B ⟶ (laxCategory p q).obj)
    (hW : ∀ e : B _⦋1⦌, f.app (Opposite.op ⦋1⦌) e ∈ tammeLocalizingEdges p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration (pullback.snd
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x) f) := by
  let π := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x
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
  have ht : (laxCategory p q).obj.δ 0 (SSet.yonedaEquiv (e ≫ f)) =
      π.app (Opposite.op ⦋0⦌) w := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hb, Equiv.apply_symm_apply]
  let s : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj)
      ((laxCategory p q).obj.δ 1 (SSet.yonedaEquiv (e ≫ f)))
      (π.app (Opposite.op ⦋0⦌) w) := ⟨SSet.yonedaEquiv (e ≫ f), rfl, ht⟩
  have hs : s.edge ∈ tammeLocalizingEdges p q := by
    dsimp only [s]
    rw [SSet.yonedaEquiv_comp]
    exact hW _
  obtain ⟨G, hG, hGπ, hGc⟩ := exists_tammeMarkedSpanCartesianLift p q x w s hs
  have hGf : G ≫ π = e ≫ f := hGπ.trans (SSet.yonedaEquiv.symm_apply_apply _)
  refine ⟨pullback.lift G e hGf, ?_, pullback.lift_snd _ _ _, ?_⟩
  · apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst, SSet.yonedaEquiv_symm_comp] using hG
    · simpa only [Category.assoc, pullback.lift_snd, SSet.yonedaEquiv_symm_comp] using he
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_pullback
    rw [← SSet.yonedaEquiv_comp, pullback.lift_fst]
    exact hGc

lemma tammeSpanBaseChange_cocartesianFibration
    (x : (laxCategory p q).obj _⦋0⦌) {B : SSet.{u}} (f : B ⟶ (laxCategory p q).obj) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (pullback.snd
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x) f) :=
  inferInstance

end SerrePositivity.KST.LocalizingInvariants
