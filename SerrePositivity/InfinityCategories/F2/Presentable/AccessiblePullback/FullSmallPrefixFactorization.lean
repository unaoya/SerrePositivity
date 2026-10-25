module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.SmallPrefixFactorization
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FactorizationEdgeLift

/-!
概要：全部分圏の全前置余錐を固定した因子化を、周囲で作って厳密に戻す。
方針：周囲の前置 coslice で filtered 余極限を判定し、制限四角形の実引き戻しを使う。
規約：全小余極限は周囲だけに要求し、元の全部分圏には追加しない。
使われ方：Ind 模型の表示添字を保つ相対一段延長。
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

/-- 概要：全部分圏の小さい compact 全図式を、元の前置余錐を固定して一段へ因子化する。
方針：周囲の全前置 coslice で因子化し、同じ制限辺を実引き戻しへ持ち上げる。
規約：元の表示の周囲での余極限性だけを入力とし、全前置制限を厳密に保持する。
使われ方：元の Ind 包含の filtered 保存性と合わせる相対因子化。 -/
lemma compactDiagram_factorization_relative_fullSubcomplex
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {J L : SSet.{u}} [Quasicategory J] [Quasicategory L]
    (hJ : IsKappaSmall μ J) (hL : IsKappaSmall μ L)
    {X : SSet.{u + 1}} [Quasicategory X] (P : X _⦋0⦌ → Prop) (hX : HasSmallColimits X)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶
      (fullSubcomplexOnVertices X P : SSet.{u + 1}))
    (hQ : ∀ j, Compact.IsKappaCompact.{u, u + 1} μ
      ((q ≫ (fullSubcomplexOnVertices X P).ι).app _ j))
    (i : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj J) [Mono i]
    {A : SSet.{u}} [Quasicategory A] [IsKappaFiltered μ A]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder (i ≫ q))
    (c : JoinCocone D)
    (hc : IsColimitCone (mapJoinCocone
      (sliceUnderProjection (i ≫ q) ≫ (fullSubcomplexOnVertices X P).ι) c))
    (z : JoinCocone q) (hz : z.restrict i = c.vertex) :
    ∃ j : A _⦋0⦌, ∃ w : JoinCocone q,
      w.restrict i = D.app _ (ULift.up j) ∧
      ∃ k : (sliceUnder q).Edge w z,
        (k.map (sliceUnderRestrict q i)).edge =
          (Compact.coconeTransportLeg c (ULift.up j)).edge := by
  let j := (fullSubcomplexOnVertices X P).ι
  let a := sliceUnderRestrict q i
  let b := sliceUnderPostcomp q j
  let f := sliceUnderPostcomp (i ≫ q) j
  let p := sliceUnderRestrict (q ≫ j) i
  let c' := mapJoinCocone f c
  have hc' : IsColimitCone c' := by
    obtain ⟨cq, hcq⟩ := hX L (i ≫ q ≫ j)
    apply (colimitSourceCoslice_isColimitCone_iff_projection (Fact.out : μ.IsRegular)
      cq hcq (D ≫ f) c').mpr
    apply (isColimitCone_iff_of_cocone_val_eq _
      (mapJoinCocone (sliceUnderProjection (i ≫ q) ≫ j) c) ?_).mpr hc
    change (c.val ≫ f) ≫ sliceUnderProjection (i ≫ (q ≫ j)) =
      c.val ≫ (sliceUnderProjection (i ≫ q) ≫ j)
    exact (Category.assoc _ _ _).trans (congrArg (fun g ↦ c.val ≫ g)
      (sliceUnderPostcomp_projection (i ≫ q) j))
  let z' : JoinCocone (q ≫ j) := b.app (Opposite.op ⦋0⦌) z
  have hz' : z'.restrict i = c'.vertex := by
    have h := congrArg (fun g ↦ g.app (Opposite.op ⦋0⦌) z)
      (sliceUnderRestrict_postcomp q i j)
    change p.app _ z' = f.app _ (a.app _ z) at h
    have hz0 : a.app (Opposite.op ⦋0⦌) z = c.vertex := hz
    rw [hz0] at h
    exact h.trans (Ind.mapJoinCocone_vertex f c).symm
  obtain ⟨k, w, hw, e, he⟩ := compactDiagram_factorization_relative_smallPrefix hμ hJ hL
    hX (q ≫ j) hQ i (D ≫ f) c' hc' z' hz'
  have he' : (e.map p).edge = ((Compact.coconeTransportLeg c (ULift.up k)).map f).edge :=
    he.trans (Compact.coconeTransportLeg_post_edge f c (ULift.up k))
  obtain ⟨v, l, hl⟩ := exists_factorizationEdge_of_isPullback a b f p
    (fullCosliceRestrict_isPullback P q i) D c (ULift.up k) z hz e he'
  exact ⟨k, v.val, v.property.trans (pinchedConstant_zero _), l, hl⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
