module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.RelativeAlternatingFactorization

/-!
概要：任意の固定小図式を含む全前置図式を、同じ成分表示内へ相対因子化する。
方針：指定成分の添字包含だけを固定し、元の Ind 表示の相対因子化を使う。
規約：全前置形状を交互順序に限定しない。
使われ方：入力した小図式を保持する相対交互塔。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility


/-- 概要：任意の全前置図式と同じ成分表示を接続する具体的因子化データ。
方針：成分添字余錐と全比較辺の制限を保持する。
規約：元の全図式とその固定対象を変更しない。
使われ方：固定小図式を伴う一段延長。 -/
structure RelativeComponentFactorization
    {J K I : SSet.{u}} {B : SSet.{u + 1}} {x : (Δ[0] : SSet.{u + 1}) ⟶ B}
    (a : J ⟶ I) (i : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj K)
    (Q : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x)
    (P : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x) where
  index : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone a
  cocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x)
  comparison : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x)).Edge cocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone Q)
  component_cone : (cocone.restrict i).val =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp ((SSet.uliftFunctor.{u + 1, u}).map a)
      (P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x)).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSliceUnderIso.{u, u + 1} a).hom.app (Opposite.op ⦋0⦌)
          (ULift.up index))).val
  component_edge : ((comparison.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) i)).edge).val =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCosliceRestrictedCocone
      ((SSet.uliftFunctor.{u + 1, u}).map a) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSliceUnderIso.{u, u + 1} a).hom
      (P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone P)) (ULift.up index)).edge).val

/-- 概要：任意の小さい全前置図式は元の成分表示を固定して相対因子化できる。
方針：元の Ind 表示への相対因子化を使い、等号輸送の生の値を回収する。
規約：元の全前置形状の終対象や余極限は不要。
使われ方：固定入力図式を含めた相対交互構成の実際の選択。 -/
lemma exists_relativeComponentFactorization
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {A : SSet.{u}} [Quasicategory A]
    {J K I : SSet.{u}} [Quasicategory J] [Quasicategory K] [Quasicategory I]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I] (hJ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ J) (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K)
    {x : (Δ[0] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A}
    (a : J ⟶ I) (i : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj K) [Mono i]
    (Q : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x)
    (P : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x)
    (hQ : ∀ v : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (hcol : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone P))
    (hi : i ≫ Q = (SSet.uliftFunctor.{u + 1, u}).map a ≫ P) :
    Nonempty (RelativeComponentFactorization a i Q P) := by
  let q := Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x
  let D := P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x
  let C := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone P
  have hp : i ≫ q = (SSet.uliftFunctor.{u + 1, u}).map a ≫ D := by
    simpa only [q, D, Category.assoc] using
      congrArg (fun f ↦ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) hi
  have hz : ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone Q).restrict i).val =
      (C.restrict ((SSet.uliftFunctor.{u + 1, u}).map a)).val := by
    have ht := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry hi
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp] at ht
    exact ht
  obtain ⟨j, w, hw, k, hk⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.compactDiagram_factorization_over_smallPrefixPresentation_ind
    hμ hK hJ a D C hcol q (by rintro ⟨v⟩; exact hQ v) i hp (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone Q) hz
  let b := (SSet.uliftFunctor.{u + 1, u}).map a
  let t := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSliceUnderIso.{u, u + 1} a).hom
  let e := eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder hp.symm)
  let V := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCosliceRestrictedCocone b t D C
  refine ⟨⟨j, w, k, ?_, ?_⟩⟩
  · exact (congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ q) ↦ z.val) hw).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnder_eqToIso_val hp.symm _)
  · calc
      _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone e.hom V) (ULift.up j)).edge.val :=
        congrArg (fun z ↦ z.val) hk
      _ = (e.hom.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg V (ULift.up j)).edge).val :=
        congrArg (fun z ↦ z.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg_post_edge e.hom V (ULift.up j))
      _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnder_eqToIso_val hp.symm _

/-- 概要：一般相対因子化から指定成分の全 slice 余錐を回収する。
方針：三因子の自然性と元の表示脚の二重 uncurry を比較する。
規約：任意の全前置形状に適用する。
使われ方：固定入力図式を保つ一段延長の成分条件。 -/
lemma RelativeComponentFactorization.component_slice
    {J K I : SSet.{u}} {B : SSet.{u + 1}} {x : (Δ[0] : SSet.{u + 1}) ⟶ B}
    {a : J ⟶ I} {i : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj K}
    {Q : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    {P : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    (t : RelativeComponentFactorization a i Q P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeSliceCocone Q t.comparison).val =
      (((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSliceUnderIso.{u, u + 1} a).hom.app (Opposite.op ⦋0⦌))
        (ULift.up t.index)).val ≫ P := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective x
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0])) (𝟙 Δ[0]) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeSliceCoconeMap Q t.comparison)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeSliceCoconeMap_right Q t.comparison)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeSliceCoconeMap]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i _), ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[1]) ≫ t.comparison.edge.val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCosliceRestrictedCocone
        ((SSet.uliftFunctor.{u + 1, u}).map a)
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSliceUnderIso.{u, u + 1} a).hom
        (P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone (P)))
          (ULift.up t.index)).edge.val := t.component_edge
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[1]) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, Category.comp_id]
  rw [hn, Category.assoc, he]
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCosliceRestrictedCocone_leg_uncurry
      ((SSet.uliftFunctor.{u + 1, u}).map a)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSliceUnderIso.{u, u + 1} a).hom
      (P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone (P)) (ULift.up t.index)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
