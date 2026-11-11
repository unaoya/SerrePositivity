module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.InitialTriangleNormalization

/-!
概要：元の二表示の実三角形から、最初の compact 全前置比較状態を構成する。
方針：小さい標準辺とその二つの端点を宇宙同型で正規化する。
規約：元の二つの全余錐を厳密に保持する。使われ方：交互比較の初期状態。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 元の点の像を、同じ持ち上げた標準零単体で表示する。 -/
lemma uliftPoint_diagram {I : SSet.{u}} {C : SSet.{u + 1}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C) (a : I _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).map (SSet.yonedaEquiv.symm a) ≫ D =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 0).hom ≫ SSet.yonedaEquiv.symm (D.app _ (ULift.up a)) := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 0).inv).mp
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftYonedaMap, SSet.yonedaEquiv_symm_comp, Iso.inv_hom_id_assoc]

/-- 二端点が compact な実辺の小さい形状表示では、全頂点が同じ濃度で compact。 -/
lemma normalizedEdge_compact {κ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C]
    {x y : C _⦋0⦌} (e : C.Edge x y)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ x) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ y) :
    ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ
      (((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 1).hom ≫ SSet.yonedaEquiv.symm e.edge).app _ v) := by
  intro v
  generalize hi : stdSimplex.obj₀Equiv v.down = i
  fin_cases i
  · have hv : v = ULift.up (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
      ULift.ext (stdSimplex.obj₀Equiv.injective (hi.trans (Equiv.apply_symm_apply _ _).symm))
    subst v
    have he : (((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 1).hom ≫
        SSet.yonedaEquiv.symm e.edge).app _
        (ULift.up (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) = x := by
      change (SSet.yonedaEquiv.symm e.edge).app _ (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = x
      have hv₀ : stdSimplex.obj₀Equiv.symm (0 : Fin 2) =
          SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2)) := by
        apply SSet.stdSimplex.ext
        intro i
        fin_cases i
        rfl
      rw [hv₀, ← SSet.yonedaEquiv_comp, stdSimplex.δ_comp_yonedaEquiv_symm,
        Equiv.apply_symm_apply, e.src_eq]
    rw [he]
    exact hx
  · have hv : v = ULift.up (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
      ULift.ext (stdSimplex.obj₀Equiv.injective (hi.trans (Equiv.apply_symm_apply _ _).symm))
    subst v
    have he : (((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 1).hom ≫
        SSet.yonedaEquiv.symm e.edge).app _
        (ULift.up (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) = y := by
      change (SSet.yonedaEquiv.symm e.edge).app _ (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = y
      have hv₁ : stdSimplex.obj₀Equiv.symm (1 : Fin 2) =
          SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2)) := by
        apply SSet.stdSimplex.ext
        intro i
        fin_cases i
        rfl
      rw [hv₁, ← SSet.yonedaEquiv_comp, stdSimplex.δ_comp_yonedaEquiv_symm,
        Equiv.apply_symm_apply, e.tgt_eq]
    rw [he]
    exact hy

/-- 元の二つの余錐脚を結ぶ実三角形は、最初の全前置比較状態を与える。 -/
def comparisonInitialState {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {C : SSet.{u + 1}} [Quasicategory C] {I₀ I₁ : SSet.{u}}
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
    (c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀) (c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁)
    (hv : c₀.vertex = c₁.vertex) (a : I₀ _⦋0⦌) (b : I₁ _⦋0⦌)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (D₀.app _ (ULift.up a)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (D₁.app _ (ULift.up b)))
    (e : C.Edge (D₀.app _ (ULift.up a)) (D₁.app _ (ULift.up b)))
    (T : e.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c₁ (ULift.up b))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c₀ (ULift.up a)).ofEq rfl hv)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactPresentationComparison κ D₀ D₁ c₀ c₁ where
  shape := Δ[1]
  shape_quasicategory := inferInstance
  shape_small := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite (Fact.out : κ.IsRegular).aleph0_le _
  diagram := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 1).hom ≫ SSet.yonedaEquiv.symm e.edge
  compact := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedEdge_compact e ha hb
  augmentation := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compStructCocone T).restrict (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 1).hom
  left_shape := Δ[0]
  left_quasicategory := inferInstance
  left_small := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite (Fact.out : κ.IsRegular).aleph0_le _
  left_terminal := stdSimplex.obj₀Equiv.symm (Fin.last 0)
  left_isTerminal := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.stdSimplex_last_isTerminalVertex 0
  left_index := SSet.yonedaEquiv.symm a
  left_inclusion := stdSimplex.δ 1
  left_mono := inferInstance
  left_diagram := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.uliftPoint_diagram]
    change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 0).hom ≫ stdSimplex.δ 1 ≫
      SSet.yonedaEquiv.symm e.edge = _
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, e.src_eq]
  left_augmentation := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedEdgeCocone_restrict_val, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compStructCocone_source_val,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.uliftPointRestriction_coconeTransportLeg_val]
    rfl
  right_shape := Δ[0]
  right_quasicategory := inferInstance
  right_small := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite (Fact.out : κ.IsRegular).aleph0_le _
  right_terminal := stdSimplex.obj₀Equiv.symm (Fin.last 0)
  right_isTerminal := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.stdSimplex_last_isTerminalVertex 0
  right_index := SSet.yonedaEquiv.symm b
  right_inclusion := stdSimplex.δ 0
  right_mono := inferInstance
  right_diagram := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.uliftPoint_diagram]
    change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 0).hom ≫ stdSimplex.δ 0 ≫
      SSet.yonedaEquiv.symm e.edge = _
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, e.tgt_eq]
  right_augmentation := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedEdgeCocone_restrict_val, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compStructCocone_target_val,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.uliftPointRestriction_coconeTransportLeg_val]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
