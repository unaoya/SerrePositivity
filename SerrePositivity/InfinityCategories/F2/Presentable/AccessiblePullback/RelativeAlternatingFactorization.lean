module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.RelativeAlternatingStage
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FixedSliceExtension

/-!
概要：元の全厳密前置段から、指定成分の同じ表示添字を延長する因子化を得る。
方針：Ind 模型内の相対因子化に全前置段の compact 性と元の全成分表示を渡す。
規約：前置段に終頂点や内部余極限を要求しない。
使われ方：長さ κ₀ の相対交互構成の実際の一段選択。
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

variable {κ : Cardinal.{u}} {B : SSet.{u + 1}}
  {x : (Δ[0] : SSet.{u + 1}) ⟶ B} {I : Fin 2 → SSet.{u}}
  {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ sliceOver x}
  {a : AlternatingIndex κ}

/-- 概要：指定成分の表示添字と全余錐の一段因子化データ。
方針：元の表示添字の全余錐と、全前置余錐の比較辺の生の値を保持する。
規約：図式表示の等号輸送を公開データの条件へ持ち込まない。
使われ方：元の段と両成分を保持する次の閉前置段。 -/
structure RelativeAlternatingFactorization
    (s : RelativeAlternatingOpenStage κ x I P a) (c : Fin 2) where
  index : JoinCocone (s.index c)
  cocone : JoinCocone (s.diagram ≫ sliceOverProjection x)
  comparison : (sliceUnder (s.diagram ≫ sliceOverProjection x)).Edge
    cocone (sliceDiagramCocone s.diagram)
  component_cone :
    (cocone.restrict ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (alternatingLowerSection κ a c)))).val =
      ((sliceUnderPostcomp ((SSet.uliftFunctor.{u + 1, u}).map (s.index c))
        (P c ≫ sliceOverProjection x)).app (Opposite.op ⦋0⦌)
          ((uliftSliceUnderIso.{u, u + 1} (s.index c)).hom.app (Opposite.op ⦋0⦌)
            (ULift.up index))).val
  component_edge :
    ((comparison.map (sliceUnderRestrict (s.diagram ≫ sliceOverProjection x)
      ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (alternatingLowerSection κ a c))))).edge).val =
      ((Compact.coconeTransportLeg (sourceCosliceRestrictedCocone
        ((SSet.uliftFunctor.{u + 1, u}).map (s.index c))
        (uliftSliceUnderIso.{u, u + 1} (s.index c)).hom
        (P c ≫ sliceOverProjection x) (sliceDiagramCocone (P c))) (ULift.up index)).edge).val

/-- 概要：元の厳密前置段から、指定成分の表示添字を保つ相対一段因子化が存在する。
方針：全前置図式の μ-small 性と compact 性を元の Ind 表示の相対因子化へ渡す。
規約：元の二つの表示と全前置段を固定し、全小余極限を追加仮定にしない。
使われ方：well-founded 相対交互塔の各再帰段での実際の選択。 -/
lemma exists_relativeAlternatingFactorization
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {A : SSet.{u}} [Quasicategory A]
    {x : (Δ[0] : SSet.{u + 1}) ⟶ Ind.IndInfinity μ A}
    {I : Fin 2 → SSet.{u}} [∀ c, Quasicategory (I c)] [∀ c, IsKappaFiltered μ (I c)]
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ sliceOver x}
    (hP : ∀ c, ∀ v : (I c) _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((P c ≫ sliceOverProjection x).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (hcol : ∀ c, IsColimitCone (sliceDiagramCocone (P c)))
    {a : AlternatingIndex κ} (s : RelativeAlternatingOpenStage κ x I P a) (c : Fin 2) :
    Nonempty (RelativeAlternatingFactorization s c) := by
  have hμ : Cardinal.aleph0 < μ :=
    (Cardinal.IsRegular.aleph0_le (Fact.out : κ.IsRegular)).trans_lt h.1
  let i := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (alternatingLowerSection κ a c))
  let q := s.diagram ≫ sliceOverProjection x
  let D := P c ≫ sliceOverProjection x
  let C := sliceDiagramCocone (P c)
  have : Mono i := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    apply (mono_iff_injective _).2
    rintro ⟨v⟩ ⟨w⟩ h
    apply ULift.ext
    have hm : Mono ((nerveMap (alternatingLowerSection κ a c)).app n) :=
      (NatTrans.mono_iff_mono_app _).mp inferInstance n
    exact (mono_iff_injective _).mp hm (congrArg ULift.down h)
  have hp : i ≫ q = (SSet.uliftFunctor.{u + 1, u}).map (s.index c) ≫ D := by
    simpa only [i, q, D, Category.assoc] using
      congrArg (fun f ↦ f ≫ sliceOverProjection x) (s.component_eq c)
  have hz : ((sliceDiagramCocone s.diagram).restrict i).val =
      (C.restrict ((SSet.uliftFunctor.{u + 1, u}).map (s.index c))).val := by
    have ht := congrArg sliceOverUncurry (s.component_eq c)
    rw [sliceOverUncurry_precomp, sliceOverUncurry_precomp] at ht
    exact ht
  obtain ⟨j, w, hw, k, hk⟩ := compactDiagram_factorization_over_smallPrefixPresentation_ind
    hμ (alternatingLower_isKappaSmall h a) (alternatingComponentLower_isKappaSmall h a c)
    (s.index c) D C (hcol c) q
    (by rintro ⟨v⟩; exact s.vertex_isKappaCompact hP v) i hp (sliceDiagramCocone s.diagram) hz
  let b := (SSet.uliftFunctor.{u + 1, u}).map (s.index c)
  let t := (uliftSliceUnderIso.{u, u + 1} (s.index c)).hom
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

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
