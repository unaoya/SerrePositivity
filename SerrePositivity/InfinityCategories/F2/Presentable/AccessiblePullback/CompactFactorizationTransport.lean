module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.TrivialFactorizationLift
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.IndCompactFactorization
public import SerrePositivity.InfinityCategories.F2.Presentable.CoslicePostcompIdentity
public import SerrePositivity.InfinityCategories.Core.EquivalencePullbackPathLifting

/-!
概要：compact 前置図式の相対因子化を自明 Kan 解像で輸送する。
方針：全図式と指定余錐を同じ射で送り、相対端点持ち上げで厳密に回収する。
規約：因子化性は証明される中間述語であり、主定理への追加入力にしない。
使われ方：一般 accessible 圏の全前置図式を保つ因子化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：全 compact 前置図式の指定余錐を、同じ filtered 表示の一段へ因子化できること。
方針：全 coslice の実辺と元の余錐脚の厳密な等式を量化する。
規約：任意の小さい quasicategory を前置図式に許す。
使われ方：Ind 模型の因子化の同値輸送。 -/
def CompactDiagramFactorization (μ : Cardinal.{u}) (C : SSet.{u + 1})
    [Quasicategory C] : Prop :=
  ∀ {J : SSet.{u}} [Quasicategory J], IsKappaSmall μ J →
    ∀ (q : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶ C),
      (∀ a, Compact.IsKappaCompact.{u, u + 1} μ (q.app _ a)) →
      ∀ {K : SSet.{u}} [Quasicategory K] [IsKappaFiltered μ K]
        (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
        (c : JoinCocone D), IsColimitCone c →
        ∀ t : (vertexFiber (sliceUnderProjection q) c.vertex) _⦋0⦌,
          ∃ i : K _⦋0⦌,
            ∃ w : (vertexFiber (sliceUnderProjection q) (D.app _ (ULift.up i))) _⦋0⦌,
              ∃ e : (sliceUnder q).Edge w.val t.val,
                (e.map (sliceUnderProjection q)).edge =
                  (Compact.coconeTransportLeg c (ULift.up i)).edge

/-- 概要：Ind 模型は全 compact 前置図式の相対因子化を持つ。
方針：前層内で証明した実余錐の因子化を中間述語にまとめる。
規約：元の Ind 模型の全小余極限は仮定しない。
使われ方：共通解像へ輸送する出発点。 -/
lemma compactDiagramFactorization_ind {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) (A : SSet.{u}) [Quasicategory A] :
    CompactDiagramFactorization μ (Ind.IndInfinity μ A) := by
  intro J hJ hsmall q hq K hK hfiltered D c hc t
  exact compactDiagram_factorization_ind hμ hsmall q hq D c hc t

/-- 概要：自明 Kan 解像の標的での因子化を元の始域へ持ち上げる。
方針：同値で compact 性と余極限を保存し、同じ脚を端点持ち上げで回収する。
規約：全前置図式と最終余錐を固定する。
使われ方：Ind 模型と元の圏の共通解像上の因子化。 -/
lemma CompactDiagramFactorization.of_trivialKan {μ : Cardinal.{u}}
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hB : CompactDiagramFactorization μ B) (p : E ⟶ B) [TrivialKanFibration p] :
    CompactDiagramFactorization μ E := by
  intro J hJ hsmall q hq K hK hfiltered D c hc t
  let e := (isQCatEquivalence_of_trivialKanFibration p).choose
  let c' := mapJoinCocone p c
  let t' := (sliceUnderPostcomp q p).app (Opposite.op ⦋0⦌) t.val
  have ht' : (sliceUnderProjection (q ≫ p)).app _ t' = c'.vertex := by
    have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) t.val)
      (sliceUnderPostcomp_projection q p)
    change (sliceUnderProjection (q ≫ p)).app _ t' =
      p.app _ ((sliceUnderProjection q).app _ t.val) at h
    rw [t.property, pinchedConstant_zero] at h
    exact h.trans (Ind.mapJoinCocone_vertex p c).symm
  let tf : (vertexFiber (sliceUnderProjection (q ≫ p)) c'.vertex) _⦋0⦌ :=
    ⟨t', ht'.trans (pinchedConstant_zero _).symm⟩
  obtain ⟨i, w, k, hk⟩ := hB hsmall (q ≫ p)
    (fun a ↦ isKappaCompact_image_of_equivalence e (q.app _ a) (hq a))
    (D ≫ p) c' (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits μ
      (isQCatEquivalence_of_trivialKanFibration p) K D c hc) tf
  have hk' : (k.map (sliceUnderProjection (q ≫ p))).edge =
      ((Compact.coconeTransportLeg c (ULift.up i)).map p).edge :=
    hk.trans (Compact.coconeTransportLeg_post_edge p c (ULift.up i))
  obtain ⟨v, l, hl⟩ := exists_factorizationEdge_of_trivialKan q p D c (ULift.up i) t k hk'
  exact ⟨i, v, l, hl⟩

private lemma stableCoslicePostcomp_vertex_val {J E B : SSet.{u + 1}}
    (a : J ⟶ E) (p : E ⟶ B) (b : J ⟶ B) (h : a ≫ p = b)
    (t : (sliceUnder a) _⦋0⦌) :
    ((stableCoslicePostcomp a p b h).app (Opposite.op ⦋0⦌) t).val = t.val ≫ p := by
  subst b
  rfl

/-- 概要：自明 Kan 射の厳密な切断を使って、相対因子化を標的へ戻す。
方針：切断で全入力を持ち上げ、得た辺を元の射で戻して指定脚を回収する。
規約：切断は元の図式と余錐の全単体に同じように適用する。
使われ方：共通解像から元の accessible 圏への因子化の降下。 -/
lemma CompactDiagramFactorization.of_trivialKan_section {μ : Cardinal.{u}}
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hE : CompactDiagramFactorization μ E) (p : E ⟶ B) [TrivialKanFibration p] :
    CompactDiagramFactorization μ B := by
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section p
  have hp := isQCatEquivalence_of_trivialKanFibration p
  have hseq : IsQCatEquivalence s := by
    apply hp.cancel_right
    rw [hs]
    exact (QCatEquivalence.refl B).isQCatEquivalence
  let se := hseq.choose
  intro J hJ hsmall q hq K hK hfiltered D c hc t
  let a := q ≫ s
  let cs := mapJoinCocone s c
  let ts := (sliceUnderPostcomp q s).app (Opposite.op ⦋0⦌) t.val
  have hts : (sliceUnderProjection a).app _ ts = cs.vertex := by
    have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) t.val)
      (sliceUnderPostcomp_projection q s)
    change (sliceUnderProjection a).app _ ts =
      s.app _ ((sliceUnderProjection q).app _ t.val) at h
    rw [t.property, pinchedConstant_zero] at h
    exact h.trans (Ind.mapJoinCocone_vertex s c).symm
  let tf : (vertexFiber (sliceUnderProjection a) cs.vertex) _⦋0⦌ :=
    ⟨ts, hts.trans (pinchedConstant_zero _).symm⟩
  obtain ⟨i, w, k, hk⟩ := hE hsmall a
    (fun z ↦ isKappaCompact_image_of_equivalence se (q.app _ z) (hq z))
    (D ≫ s) cs (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits μ hseq K D c hc) tf
  have hap : a ≫ p = q := by
    dsimp [a]
    rw [Category.assoc, hs, Category.comp_id]
  let R := stableCoslicePostcomp a p q hap
  have hRt : R.app (Opposite.op ⦋0⦌) tf.val = t.val := by
    apply Subtype.ext
    rw [stableCoslicePostcomp_vertex_val]
    change (t.val.val ≫ s) ≫ p = t.val.val
    rw [Category.assoc, hs, Category.comp_id]
  let z := R.app (Opposite.op ⦋0⦌) w.val
  let kr : (sliceUnder q).Edge z t.val :=
    ⟨(k.map R).edge, (k.map R).src_eq, (k.map R).tgt_eq.trans hRt⟩
  have hkr : (kr.map (sliceUnderProjection q)).edge =
      (Compact.coconeTransportLeg c (ULift.up i)).edge := by
    calc
      _ = (k.map (sliceUnderProjection a ≫ p)).edge :=
        congrArg (fun g ↦ g.app _ k.edge) (stableCoslicePostcomp_projection a p q hap)
      _ = p.app _ (Compact.coconeTransportLeg cs (ULift.up i)).edge :=
        congrArg (fun v ↦ p.app _ v) hk
      _ = p.app _ ((Compact.coconeTransportLeg c (ULift.up i)).map s).edge :=
        congrArg (fun v ↦ p.app _ v) (Compact.coconeTransportLeg_post_edge s c (ULift.up i))
      _ = (Compact.coconeTransportLeg c (ULift.up i)).edge := by
        change (s ≫ p).app _ _ = _
        rw [hs]
        rfl
  have hz : (sliceUnderProjection q).app _ z = D.app _ (ULift.up i) := by
    calc
      _ = B.δ 1 (kr.map (sliceUnderProjection q)).edge :=
        (kr.map (sliceUnderProjection q)).src_eq.symm
      _ = B.δ 1 (Compact.coconeTransportLeg c (ULift.up i)).edge := congrArg (B.δ 1) hkr
      _ = _ := (Compact.coconeTransportLeg c (ULift.up i)).src_eq
  exact ⟨i, ⟨z, hz.trans (pinchedConstant_zero _).symm⟩, kr, hkr⟩

/-- 概要：任意の μ-accessible 圏で全 compact 前置図式の相対因子化ができる。
方針：Ind 表示同値の共通解像の二つの自明 Kan 射で因子化を輸送する。
規約：元の圏の全小余極限や前置図式の内部余極限を仮定しない。
使われ方：長さ κ₀ の交互構成の極限段で全前置図式を固定する。 -/
lemma compactDiagramFactorization_of_isKappaAccessible
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : IsKappaAccessible μ C) :
    CompactDiagramFactorization μ C := by
  obtain ⟨A, hA, ⟨e⟩⟩ := hC.exists_indEquivalence
  have := hA
  let s := equivalencePathReplacementProjection e.hom
  let r := equivalencePathReplacementMap e.hom
  have : TrivialKanFibration r :=
    e.isQCatEquivalence.equivalencePathReplacementMap_trivialKanFibration
  have hz : CompactDiagramFactorization μ (equivalencePathReplacement e.hom) :=
    CompactDiagramFactorization.of_trivialKan (compactDiagramFactorization_ind hμ A) s
  intro J hJ hsmall q hq K hK hfiltered D c hc t
  exact CompactDiagramFactorization.of_trivialKan_section
    (E := equivalencePathReplacement e.hom) (B := C) (μ := μ) hz r hsmall q hq D c hc t

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
