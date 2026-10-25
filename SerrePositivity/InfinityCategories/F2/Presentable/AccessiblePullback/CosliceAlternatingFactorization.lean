module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.CosliceIndRelativePresentation
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.RelativeAlternatingFactorization

/-!
概要：固定始域内で両成分入力を保持する相対交互構成の一段因子化。
方針：元の Ind 圏への射影で compact 性を判定し、固定始域内の相対因子化を使う。
規約：成分入力からの全射を保持し、底だけの入力保持から生成性を結論しない。
使われ方：元の両成分の小入力図式を保持する交互塔。
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

/-- 概要：厳密前置段の全頂点は射影後にも成分表示と同じ compact 性を持つ。
方針：各頂点を元の成分から回収し、全成分等式を射影する。
規約：compact 性は指定された元の標的で判定する。
使われ方：固定始域内の図式の元の Ind 圏での compact 性。 -/
lemma RelativeAlternatingOpenStage.vertex_image_isKappaCompact
    {μ κ : Cardinal.{u}} {B C : SSet.{u + 1}} [Quasicategory C]
    {x : (Δ[0] : SSet.{u + 1}) ⟶ B} {I : Fin 2 → SSet.{u}}
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ sliceOver x}
    {a : AlternatingIndex κ} (s : RelativeAlternatingOpenStage κ x I P a) (f : B ⟶ C)
    (hP : ∀ c, ∀ v : (I c) _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((P c ≫ sliceOverProjection x ≫ f).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (v : (nerve (AlternatingLower κ a)) _⦋0⦌) :
    Compact.IsKappaCompact.{u, u + 1} μ
      ((s.diagram ≫ sliceOverProjection x ≫ f).app (Opposite.op ⦋0⦌) (ULift.up v)) := by
  obtain ⟨c, w, hw⟩ := alternatingLower_vertex_component a v
  have h := congrArg (fun g ↦ g.app (Opposite.op ⦋0⦌) (ULift.up w)) (s.component_eq c)
  change s.diagram.app (Opposite.op ⦋0⦌)
      (ULift.up ((nerveMap (alternatingLowerSection κ a c)).app (Opposite.op ⦋0⦌) w)) =
    (P c).app (Opposite.op ⦋0⦌) (ULift.up ((s.index c).app (Opposite.op ⦋0⦌) w)) at h
  rw [hw] at h
  have h' := congrArg (fun z ↦ (sliceOverProjection x ≫ f).app (Opposite.op ⦋0⦌) z) h
  exact h'.symm ▸ hP c ((s.index c).app (Opposite.op ⦋0⦌) w)

/-- 概要：元の厳密前置段から、指定成分の表示添字を保つ相対一段因子化が存在する。
方針：全前置図式の μ-small 性と compact 性を元の Ind 表示の相対因子化へ渡す。
規約：元の二つの表示と全前置段を固定し、全小余極限を追加仮定にしない。
使われ方：well-founded 相対交互塔の各再帰段での実際の選択。 -/
lemma exists_relativeAlternatingFactorization_coslice_ind
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {A S : SSet.{u}} [Quasicategory A] [Quasicategory S]
    (hS : IsKappaSmall μ S)
    (s₀ : (SSet.uliftFunctor.{u + 1, u}).obj S ⟶ Ind.IndInfinity μ A)
    (hs₀ : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ (s₀.app (Opposite.op ⦋0⦌) v))
    {x : (Δ[0] : SSet.{u + 1}) ⟶ sliceUnder s₀}
    {I : Fin 2 → SSet.{u}} [∀ c, Quasicategory (I c)] [∀ c, IsKappaFiltered μ (I c)]
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ sliceOver x}
    (hP : ∀ c, ∀ v : (I c) _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((P c ≫ sliceOverProjection x ≫ sliceUnderProjection s₀).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (hcol : ∀ c, IsColimitCone (mapJoinCocone (sliceUnderProjection s₀)
      (sliceDiagramCocone (P c))))
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
  obtain ⟨j, w, hw, k, hk⟩ := compactDiagram_factorization_over_smallPrefixPresentation_coslice_ind
    hμ hS s₀ hs₀ (alternatingLower_isKappaSmall h a) (alternatingComponentLower_isKappaSmall h a c)
    (s.index c) D C (hcol c) q
    (by rintro ⟨v⟩; exact s.vertex_image_isKappaCompact (sliceUnderProjection s₀) hP v) i hp (sliceDiagramCocone s.diagram) hz
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
