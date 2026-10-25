module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.RelativeAlternatingFactorization

/-!
概要：任意の固定小図式を含む全前置図式を、同じ成分表示内へ相対因子化する。
方針：指定成分の添字包含だけを固定し、元の Ind 表示の相対因子化を使う。
規約：全前置形状を交互順序に限定しない。
使われ方：入力した小図式を保持する相対交互塔。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
open HomotopyLimits

/-- 概要：任意の全前置図式と同じ成分表示を接続する具体的因子化データ。
方針：成分添字余錐と全比較辺の制限を保持する。
規約：元の全図式とその固定対象を変更しない。
使われ方：固定小図式を伴う一段延長。 -/
structure RelativeComponentFactorization
    {J K I : SSet.{u}} {B : SSet.{u + 1}} {x : (Δ[0] : SSet.{u + 1}) ⟶ B}
    (a : J ⟶ I) (i : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj K)
    (Q : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceOver x)
    (P : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ sliceOver x) where
  index : JoinCocone a
  cocone : JoinCocone (Q ≫ sliceOverProjection x)
  comparison : (sliceUnder (Q ≫ sliceOverProjection x)).Edge cocone (sliceDiagramCocone Q)
  component_cone : (cocone.restrict i).val =
    ((sliceUnderPostcomp ((SSet.uliftFunctor.{u + 1, u}).map a)
      (P ≫ sliceOverProjection x)).app (Opposite.op ⦋0⦌)
        ((uliftSliceUnderIso.{u, u + 1} a).hom.app (Opposite.op ⦋0⦌)
          (ULift.up index))).val
  component_edge : ((comparison.map (sliceUnderRestrict (Q ≫ sliceOverProjection x) i)).edge).val =
    ((Compact.coconeTransportLeg (sourceCosliceRestrictedCocone
      ((SSet.uliftFunctor.{u + 1, u}).map a) (uliftSliceUnderIso.{u, u + 1} a).hom
      (P ≫ sliceOverProjection x) (sliceDiagramCocone P)) (ULift.up index)).edge).val

/-- 概要：任意の小さい全前置図式は元の成分表示を固定して相対因子化できる。
方針：元の Ind 表示への相対因子化を使い、等号輸送の生の値を回収する。
規約：元の全前置形状の終対象や余極限は不要。
使われ方：固定入力図式を含めた相対交互構成の実際の選択。 -/
lemma exists_relativeComponentFactorization
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {A : SSet.{u}} [Quasicategory A]
    {J K I : SSet.{u}} [Quasicategory J] [Quasicategory K] [Quasicategory I]
    [IsKappaFiltered μ I] (hJ : IsKappaSmall μ J) (hK : IsKappaSmall μ K)
    {x : (Δ[0] : SSet.{u + 1}) ⟶ Ind.IndInfinity μ A}
    (a : J ⟶ I) (i : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj K) [Mono i]
    (Q : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceOver x)
    (P : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ sliceOver x)
    (hQ : ∀ v : K _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((Q ≫ sliceOverProjection x).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (hcol : IsColimitCone (sliceDiagramCocone P))
    (hi : i ≫ Q = (SSet.uliftFunctor.{u + 1, u}).map a ≫ P) :
    Nonempty (RelativeComponentFactorization a i Q P) := by
  let q := Q ≫ sliceOverProjection x
  let D := P ≫ sliceOverProjection x
  let C := sliceDiagramCocone P
  have hp : i ≫ q = (SSet.uliftFunctor.{u + 1, u}).map a ≫ D := by
    simpa only [q, D, Category.assoc] using
      congrArg (fun f ↦ f ≫ sliceOverProjection x) hi
  have hz : ((sliceDiagramCocone Q).restrict i).val =
      (C.restrict ((SSet.uliftFunctor.{u + 1, u}).map a)).val := by
    have ht := congrArg sliceOverUncurry hi
    rw [sliceOverUncurry_precomp, sliceOverUncurry_precomp] at ht
    exact ht
  obtain ⟨j, w, hw, k, hk⟩ := compactDiagram_factorization_over_smallPrefixPresentation_ind
    hμ hK hJ a D C hcol q (by rintro ⟨v⟩; exact hQ v) i hp (sliceDiagramCocone Q) hz
  let b := (SSet.uliftFunctor.{u + 1, u}).map a
  let t := (uliftSliceUnderIso.{u, u + 1} a).hom
  let e := eqToIso (congrArg sliceUnder hp.symm)
  let V := sourceCosliceRestrictedCocone b t D C
  refine ⟨⟨j, w, k, ?_, ?_⟩⟩
  · exact (congrArg (fun z : JoinCocone (i ≫ q) ↦ z.val) hw).trans
      (Ind.sliceUnder_eqToIso_val hp.symm _)
  · calc
      _ = (Compact.coconeTransportLeg (mapJoinCocone e.hom V) (ULift.up j)).edge.val :=
        congrArg (fun z ↦ z.val) hk
      _ = (e.hom.app (Opposite.op ⦋1⦌) (Compact.coconeTransportLeg V (ULift.up j)).edge).val :=
        congrArg (fun z ↦ z.val) (Compact.coconeTransportLeg_post_edge e.hom V (ULift.up j))
      _ = _ := Ind.sliceUnder_eqToIso_val hp.symm _

/-- 概要：一般相対因子化から指定成分の全 slice 余錐を回収する。
方針：三因子の自然性と元の表示脚の二重 uncurry を比較する。
規約：任意の全前置形状に適用する。
使われ方：固定入力図式を保つ一段延長の成分条件。 -/
lemma RelativeComponentFactorization.component_slice
    {J K I : SSet.{u}} {B : SSet.{u + 1}} {x : (Δ[0] : SSet.{u + 1}) ⟶ B}
    {a : J ⟶ I} {i : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj K}
    {Q : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceOver x}
    {P : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ sliceOver x}
    (t : RelativeComponentFactorization a i Q P) :
    joinMap i (𝟙 Δ[0]) ≫ (relativeSliceCocone Q t.comparison).val =
      (((uliftSliceUnderIso.{u, u + 1} a).hom.app (Opposite.op ⦋0⦌))
        (ULift.up t.index)).val ≫ P := by
  apply sliceOverUncurry_injective x
  rw [sliceOverUncurry_precomp, sliceOverUncurry_precomp]
  change joinMap (joinMap i (𝟙 Δ[0])) (𝟙 Δ[0]) ≫
      sliceOverUncurry (sliceOverCurry (relativeSliceCoconeMap Q t.comparison)
        (relativeSliceCoconeMap_right Q t.comparison)) = _
  rw [sliceOverUncurry_curry, relativeSliceCoconeMap]
  rw [← Category.assoc, joinAssociator_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (joinMap i _), ← joinMap_comp, Category.comp_id,
    joinMap_id, Category.id_comp, sliceUnderUncurry_yoneda]
  have he : joinMap i (𝟙 Δ[1]) ≫ t.comparison.edge.val =
      (Compact.coconeTransportLeg (sourceCosliceRestrictedCocone
        ((SSet.uliftFunctor.{u + 1, u}).map a)
        (uliftSliceUnderIso.{u, u + 1} a).hom
        (P ≫ sliceOverProjection x) (sliceDiagramCocone (P)))
          (ULift.up t.index)).edge.val := t.component_edge
  have hn : joinMap i (joinStdSimplexIso 0 0).hom =
      joinMap (𝟙 _) (joinStdSimplexIso 0 0).hom ≫ joinMap i (𝟙 Δ[1]) := by
    rw [← joinMap_comp, Category.id_comp, Category.comp_id]
  rw [hn, Category.assoc, he]
  simpa only [sliceUnderUncurry_yoneda, sliceDiagramCocone] using
    sourceCosliceRestrictedCocone_leg_uncurry
      ((SSet.uliftFunctor.{u + 1, u}).map a)
      (uliftSliceUnderIso.{u, u + 1} a).hom
      (P ≫ sliceOverProjection x) (sliceDiagramCocone (P)) (ULift.up t.index)

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
