module

public import SerrePositivity.InfinityCategories.F2.Presentable.CompactSourceSliceRestriction
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPullbackModels
public import SerrePositivity.InfinityCategories.F2.Presentable.PullbackSliceComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.ComponentCompactOverCocones
public import SerrePositivity.InfinityCategories.F2.Presentable.SlicePostcompEquivalenceLifting

/-!
概要：compact 成分を持つ元の対象上の comma に小さい全同値模型を与える。
方針：全 slice の引き戻しを compact 始域で制限し、三つの小模型を貼り合わせる。
規約：全余極限保存を仮定せず、成分の accessibility と compact 保存を明示する。
使われ方：点 fiber の compact comma の小さい filtered 添字。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

private lemma overPostcomp_projection {C D : SSet.{u + 1}}
    (x : (Δ[0] : SSet.{u + 1}) ⟶ C) (G : C ⟶ D) :
    sliceOverPostcomp x G ≫ sliceOverProjection (x ≫ G) = sliceOverProjection x ≫ G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (joinInl (stdSimplex.obj n.unop) Δ[0] ≫ (s.val ≫ G)) =
    G.app n (SSet.yonedaEquiv (joinInl (stdSimplex.obj n.unop) Δ[0] ≫ s.val))
  rw [← Category.assoc, SSet.yonedaEquiv_comp]

private lemma pullbackBase_projection {E D B : SSet.{u + 1}}
    (p : E ⟶ B) (q : D ⟶ B) (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q) :
    pullbackSliceBaseMap p q x ≫ sliceOverProjection ((x ≫ pullback.fst p q) ≫ p) =
      sliceOverProjection (x ≫ pullback.snd p q) ≫ q := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (joinInl (stdSimplex.obj n.unop) Δ[0] ≫ (s.val ≫ q)) =
    q.app n (SSet.yonedaEquiv (joinInl (stdSimplex.obj n.unop) Δ[0] ≫ s.val))
  rw [← Category.assoc, SSet.yonedaEquiv_comp]

/-- 概要：compact 両成分の対象上の comma は小模型を持つ。
方針：全 slice の厳密な引き戻しを compact 始域で制限し、成分の小模型を移す。
規約：点射を含み、両脚の全小余極限保存は不要。
使われ方：compact comma の filtered 性と生成表示の添字。 -/
lemma exists_smallComponentCompactOverModel {μ : Cardinal.{u}}
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : F1B.EquivalenceLifting p)
    (hE : IsKappaAccessible μ E) (hD : IsKappaAccessible μ D)
    (hB : IsKappaAccessible μ B)
    (hpc : ∀ e, Compact.IsKappaCompact.{u, u + 1} μ e →
      Compact.IsKappaCompact.{u, u + 1} μ (p.app _ e))
    (hqc : ∀ d, Compact.IsKappaCompact.{u, u + 1} μ d →
      Compact.IsKappaCompact.{u, u + 1} μ (q.app _ d))
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q) :
    letI := hp.innerFibration
    ∃ (A : SSet.{u}) (hA : Quasicategory A), letI := hA
      Nonempty (QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
        (componentCompactOver μ p q x)) := by
  have : InnerFibration p := hp.innerFibration
  let xe := x ≫ pullback.fst p q
  let xd := x ≫ pullback.snd p q
  let xb := xe ≫ p
  let fp := sliceOverPostcomp xe p
  let fq := pullbackSliceBaseMap p q x
  have hfp : fp ≫ sliceOverProjection xb = sliceOverProjection xe ≫ p :=
    overPostcomp_projection xe p
  have hfq : fq ≫ sliceOverProjection xb = sliceOverProjection xd ≫ q :=
    pullbackBase_projection p q x
  let P := fun v : (sliceOver x) _⦋0⦌ ↦
    ComponentCompactVertex μ p q ((sliceOverProjection x).app _ v)
  let PE := fun v : (sliceOver xe) _⦋0⦌ ↦
    Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection xe).app _ v)
  let PD := fun v : (sliceOver xd) _⦋0⦌ ↦
    Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection xd).app _ v)
  let PB := fun v : (sliceOver xb) _⦋0⦌ ↦
    Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection xb).app _ v)
  let re := sliceOverPostcomp x (pullback.fst p q)
  let rd := sliceOverPostcomp x (pullback.snd p q)
  have hre := overPostcomp_projection x (pullback.fst p q)
  have hrd := overPostcomp_projection x (pullback.snd p q)
  let je := fullSubcomplexLift PE ((fullSubcomplexOnVertices (sliceOver x) P).ι ≫ re)
    (fun v ↦ by
      have hv := (fullSubcomplexOnVertices_vertex v).1
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app hre (Opposite.op ⦋0⦌)) v.val
      change PE (re.app _ v.val)
      dsimp only [PE]
      change Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection xe).app _ (re.app _ v.val))
      rw [show (sliceOverProjection xe).app _ (re.app _ v.val) =
        (pullback.fst p q).app _ ((sliceOverProjection x).app _ v.val) from he]
      exact hv)
  let jd := fullSubcomplexLift PD ((fullSubcomplexOnVertices (sliceOver x) P).ι ≫ rd)
    (fun v ↦ by
      have hv := (fullSubcomplexOnVertices_vertex v).2
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app hrd (Opposite.op ⦋0⦌)) v.val
      change PD (rd.app _ v.val)
      dsimp only [PD]
      change Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection xd).app _ (rd.app _ v.val))
      rw [show (sliceOverProjection xd).app _ (rd.app _ v.val) =
        (pullback.snd p q).app _ ((sliceOverProjection x).app _ v.val) from he]
      exact hv)
  let rp := compactSourceSliceRestriction μ p fp hfp hpc
  let rq := compactSourceSliceRestriction μ q fq hfq hqc
  have hraw : IsPullback re rd fp fq :=
    IsPullback.of_iso_pullback (CommSq.mk (pullbackSlice_condition p q x))
      (pullbackSliceIso p q x) (pullbackSliceIso_hom_fst p q x)
      (pullbackSliceIso_hom_snd p q x)
  have hr : IsPullback je jd rp rq :=
    isPullback_fullSubcomplex_restriction hraw P PE PD PB je jd rp rq
      (fullSubcomplexLift_ι _ _ _) (fullSubcomplexLift_ι _ _ _)
      (compactSourceSliceRestriction_inclusion μ p fp hfp hpc)
      (compactSourceSliceRestriction_inclusion μ q fq hfq hqc) (fun v he hd ↦ by
        have he' := ConcreteCategory.congr_hom (NatTrans.congr_app hre (Opposite.op ⦋0⦌)) v
        have hd' := ConcreteCategory.congr_hom (NatTrans.congr_app hrd (Opposite.op ⦋0⦌)) v
        exact ⟨(congrArg (Compact.IsKappaCompact.{u, u + 1} μ) he').mp he,
          (congrArg (Compact.IsKappaCompact.{u, u + 1} μ) hd').mp hd⟩)
  have hrp : F1B.EquivalenceLifting rp :=
    compactSourceSliceRestriction_equivalenceLifting μ p fp hfp hpc
      (sliceOverPostcomp_equivalenceLifting xe p hp)
  obtain ⟨A, hA, ⟨a⟩⟩ := hE.exists_smallCompactSourceSliceModel xe
  obtain ⟨K, hK, ⟨k⟩⟩ := hD.exists_smallCompactSourceSliceModel xd
  obtain ⟨L, hL, ⟨l⟩⟩ := hB.exists_smallCompactSourceSliceModel xb
  have := hA
  have := hK
  have := hL
  obtain ⟨T, hT, ⟨t⟩⟩ := exists_smallStrictPullbackModel_of_component_models a k l rp rq hrp
  have := hT
  have : InnerFibration rp := hrp.innerFibration
  exact ⟨T, hT, ⟨t.trans (qCatEquivalenceOfIso hr.isoPullback.symm)⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
