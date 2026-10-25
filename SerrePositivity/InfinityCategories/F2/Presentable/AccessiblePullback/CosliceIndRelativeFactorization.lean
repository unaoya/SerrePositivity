module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.ExpandedSourcePrefix

/-!
概要：固定始域の下の Ind 図式で、全前置条件を保つ相対因子化を構成する。
方針：入力と前置図式を全展開し、既存の Ind 因子化と余錐圏の引き戻しを使う。
規約：固定始域と全比較辺を保持し、coslice の全余完備性を仮定しない。
使われ方：元の両成分の入力からの射を保持する相対交互構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

private lemma eq_coslice_projection {K C : SSet.{u}} {f g : K ⟶ C} (h : f = g) :
    (eqToIso (congrArg sliceUnder h)).hom ≫ sliceUnderProjection g = sliceUnderProjection f := by
  subst g
  rfl

/-- 概要：固定始域の下の Ind 図式で全前置条件を保つ実際の相対因子化が存在する。
方針：全 join 図式を同じ Ind 模型で因子化し、厳密な余錐圏同型の四角形で辺を戻す。
規約：底における同じ filtered 余極限だけを使う。
使われ方：固定された成分入力を伴う長さ κ₀ の相対交互構成。 -/
lemma compactDiagram_factorization_relative_coslice_ind
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {B S J L : SSet.{u}} [Quasicategory B] [Quasicategory S]
    [Quasicategory J] [Quasicategory L]
    (hS : IsKappaSmall μ S) (hJ : IsKappaSmall μ J) (hL : IsKappaSmall μ L)
    (a : (SSet.uliftFunctor.{u + 1, u}).obj S ⟶ Ind.IndInfinity μ B)
    (ha : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ (a.app (Opposite.op ⦋0⦌) v))
    (q : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶ sliceUnder a)
    (hq : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ
      ((q ≫ sliceUnderProjection a).app (Opposite.op ⦋0⦌) v))
    (i : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj J) [Mono i]
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ sliceUnder (i ≫ q))
    (c : JoinCocone D)
    (hc : IsColimitCone (mapJoinCocone
      (sliceUnderProjection (i ≫ q) ≫ sliceUnderProjection a) c))
    (z : JoinCocone q) (hz : z.restrict i = c.vertex) :
    ∃ j : I _⦋0⦌, ∃ w : JoinCocone q,
      w.restrict i = D.app (Opposite.op ⦋0⦌) (ULift.up j) ∧
      ∃ k : (sliceUnder q).Edge w z,
        (k.map (sliceUnderRestrict q i)).edge =
          (Compact.coconeTransportLeg c (ULift.up j)).edge := by
  let e := uliftJoinIso.{u, u + 1} S J
  let e' := uliftJoinIso.{u, u + 1} S L
  let Q := e.hom ≫ sliceUnderUncurry q
  let f := expandedSourcePrefixMap e e' i
  have hf : f ≫ Q = e'.hom ≫ sliceUnderUncurry (i ≫ q) :=
    expandedSourcePrefixMap_diagram q e e' i
  let G := fixedSourceUncurryIso q e
  let H := fixedSourceUncurryIso (i ≫ q) e' ≪≫ eqToIso (congrArg sliceUnder hf.symm)
  have : Mono f := expandedSourcePrefixMap_mono e e' i
  have hsq : IsPullback (sliceUnderRestrict q i) G.hom H.hom (sliceUnderRestrict Q f) := by
    apply IsPullback.of_vert_isIso
    constructor
    apply (cancel_mono (eqToIso (congrArg sliceUnder hf)).hom).1
    change ((sliceUnderRestrict q i) ≫
      ((fixedSourceUncurryIso (i ≫ q) e').hom ≫
        (eqToIso (congrArg sliceUnder hf.symm)).hom)) ≫ _ = _
    rw [Category.assoc, Category.assoc]
    have heq : (eqToIso (congrArg sliceUnder hf.symm)).hom ≫
        (eqToIso (congrArg sliceUnder hf)).hom = 𝟙 _ := by
      change eqToHom (congrArg sliceUnder hf.symm) ≫
        eqToHom (congrArg sliceUnder hf) = _
      simp
    rw [heq, Category.comp_id]
    exact (fixedSourceUncurryIso_prefix q e e' i).symm
  have hQ : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ (Q.app (Opposite.op ⦋0⦌) v) := by
    rintro ⟨v⟩
    rcases join_vertex_cases v with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · have h := congrArg (fun F ↦ F.app (Opposite.op ⦋0⦌) (ULift.up w))
        (fixedSourceShapeDiagram_inl q)
      exact h.symm ▸ ha (ULift.up w)
    · have h := congrArg (fun F ↦ F.app (Opposite.op ⦋0⦌) (ULift.up w))
        (fixedSourceShapeDiagram_inr q)
      exact h.symm ▸ hq (ULift.up w)
  let D' := D ≫ H.hom
  let c' := mapJoinCocone H.hom c
  have hH : H.hom ≫ sliceUnderProjection (f ≫ Q) =
      sliceUnderProjection (i ≫ q) ≫ sliceUnderProjection a := by
    simp only [H, Iso.trans_hom, Category.assoc]
    rw [eq_coslice_projection hf.symm, fixedSourceUncurryIso_projection]
  have hc' : IsColimitCone (mapJoinCocone (sliceUnderProjection (f ≫ Q)) c') := by
    apply (isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr hc
    change (c.val ≫ H.hom) ≫ sliceUnderProjection (f ≫ Q) =
      c.val ≫ (sliceUnderProjection (i ≫ q) ≫ sliceUnderProjection a)
    rw [Category.assoc, hH]
  let z' : JoinCocone Q := G.hom.app (Opposite.op ⦋0⦌) z
  have hz' : z'.restrict f = c'.vertex := by
    have h := congrArg (fun F ↦ F.app (Opposite.op ⦋0⦌) z) hsq.w
    change H.hom.app _ (z.restrict i) = z'.restrict f at h
    rw [hz] at h
    exact h.symm.trans (Ind.mapJoinCocone_vertex H.hom c).symm
  obtain ⟨j, w, hw, k, hk⟩ := compactDiagram_factorization_relative_ind hμ
    (isKappaSmall_join (Fact.out : μ.IsRegular) hS hJ)
    (isKappaSmall_join (Fact.out : μ.IsRegular) hS hL) Q hQ f D' c' hc' z' hz'
  have hk' : (k.map (sliceUnderRestrict Q f)).edge =
      ((Compact.coconeTransportLeg c (ULift.up j)).map H.hom).edge :=
    hk.trans (Compact.coconeTransportLeg_post_edge H.hom c (ULift.up j))
  obtain ⟨v, l, hl⟩ := exists_factorizationEdge_of_isPullback
    (sliceUnderRestrict q i) G.hom H.hom (sliceUnderRestrict Q f)
    hsq D c (ULift.up j) z hz k hk'
  refine ⟨j, v.val, ?_, l, hl⟩
  exact v.property.trans (pinchedConstant_zero _)

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
