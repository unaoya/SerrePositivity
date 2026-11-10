module

public import SerrePositivity.InfinityCategories.F2.Presentable.CompactIndYonedaModel
public import SerrePositivity.InfinityCategories.F2.Presentable.IndEquivalenceDensity
public import SerrePositivity.InfinityCategories.F2.Presentable.RightFibrationEquivalenceLifting
public import SerrePositivity.InfinityCategories.F2.Presentable.RelativeSliceCocone
public import SerrePositivity.InfinityCategories.F1.Equivalences.EquivalenceLiftingPullback
public import SerrePositivity.InfinityCategories.F2.Ind.EquivalentCoconeRestriction

/-!
概要：元の対象への全 compact 始域 slice の標準余錐は元の対象の余極限となる。
方針：全 compact 小模型の実 Ind Yoneda 像を使い、標準左 Kan 余錐を底変換同値で移す。
規約：元の全 slice と元の固定対象を保持する。
使われ方：compact fiber comma の小さい標準余錐の余極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：compact 小模型の左 Kan 添字から元の compact 始域 slice への全比較。
方針：始域射影の頂点条件逆像の実引き戻しで二射影を貼り合わせる。
規約：元の全 slice への包含を厳密に保つ。
使われ方：元の標準密度余錐の添字比較。 -/
def compactSourceSliceKanComparison {μ : Cardinal.{u}}
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    (f : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
      (Compact.kappaCompactObjects.{u, u + 1} μ C)) (y : C _⦋0⦌) :
    leftKanShape (f.hom ≫ Compact.kappaCompactInclusion.{u, u + 1} μ C) y ⟶
      compactSourceSlice μ (SSet.yonedaEquiv.symm y) :=
  (predicatePreimage_isPullback (sliceOverProjection (SSet.yonedaEquiv.symm y))
    (Compact.IsKappaCompact.{u, u + 1} μ)).lift
      (pullback.snd _ _) (pullback.fst _ _ ≫ f.hom) (by
        rw [Category.assoc, ← pullback.condition]
        rfl)

/-- 概要：同じ添字比較は元の全 slice 図式を保持する。
方針：頂点条件逆像の引き戻しの第一射影。
規約：全射の厳密な等式。
使われ方：標準全余錐値の同定。 -/
lemma compactSourceSliceKanComparison_inclusion {μ : Cardinal.{u}}
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    (f : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
      (Compact.kappaCompactObjects.{u, u + 1} μ C)) (y : C _⦋0⦌) :
    compactSourceSliceKanComparison f y ≫
      (fullSubcomplexOnVertices (sliceOver (SSet.yonedaEquiv.symm y))
        (fun v ↦ Compact.IsKappaCompact.{u, u + 1} μ
          ((sliceOverProjection (SSet.yonedaEquiv.symm y)).app _ v))).ι =
      pullback.snd (f.hom ≫ Compact.kappaCompactInclusion.{u, u + 1} μ C)
        (sliceOverProjection (SSet.yonedaEquiv.symm y)) :=
  (predicatePreimage_isPullback (sliceOverProjection (SSet.yonedaEquiv.symm y))
    (Compact.IsKappaCompact.{u, u + 1} μ)).lift_fst _ _ _

/-- 概要：全 compact 小模型による同じ左 Kan 添字比較は全同値。
方針：実引き戻しの貼り合わせと right fibration に沿う模型同値の底変換を使う。
規約：元の小模型と元の slice を保持する。
使われ方：標準全余錐の余極限性の移送。 -/
lemma compactSourceSliceKanComparison_isQCatEquivalence {μ : Cardinal.{u}}
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    (f : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
      (Compact.kappaCompactObjects.{u, u + 1} μ C)) (y : C _⦋0⦌) :
    IsQCatEquivalence (compactSourceSliceKanComparison f y) := by
  let a := SSet.yonedaEquiv.symm y
  let j := Compact.kappaCompactInclusion.{u, u + 1} μ C
  let P := compactSourceSliceProjection μ a
  have : RightFibration (leftKanProjection (f.hom ≫ j) y) :=
    ⟨rightFibrations.pullback_fst _ _ RightFibration.mem⟩
  have : Quasicategory (leftKanShape (f.hom ≫ j) y) :=
    quasicategory_of_innerFibration (leftKanProjection (f.hom ≫ j) y)
  have ht := predicatePreimage_isPullback (sliceOverProjection a)
    (Compact.IsKappaCompact.{u, u + 1} μ)
  have hwhole : IsPullback (pullback.snd (f.hom ≫ j) (sliceOverProjection a))
      (pullback.fst (f.hom ≫ j) (sliceOverProjection a)) (sliceOverProjection a) (f.hom ≫ j) :=
    (IsPullback.of_hasPullback (f.hom ≫ j) (sliceOverProjection a)).flip
  have hpb : IsPullback (compactSourceSliceKanComparison f y)
      (leftKanProjection (f.hom ≫ j) y) P f.hom := IsPullback.of_right' hwhole ht
  have hfst : IsQCatEquivalence (pullback.fst P f.hom) := by
    have h := f.isQCatEquivalence.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting
      P (rightFibration_equivalenceLifting P)
    have hc := (qCatEquivalenceOfIso (pullbackSymmetry P f.hom)).isQCatEquivalence.comp
      h.isQCatEquivalence
    change IsQCatEquivalence ((pullbackSymmetry P f.hom).hom ≫ pullback.snd f.hom P) at hc
    simpa only [pullbackSymmetry_hom_comp_snd] using hc
  have : RightFibration (pullback.snd P f.hom) :=
    ⟨rightFibrations.pullback_snd _ _ RightFibration.mem⟩
  have : Quasicategory (pullback P f.hom) :=
    quasicategory_of_innerFibration (pullback.snd P f.hom)
  have hc := (qCatEquivalenceOfIso hpb.isoPullback).isQCatEquivalence.comp hfst
  exact (congrArg (fun g ↦ IsQCatEquivalence g) hpb.isoPullback_hom_fst).mp hc

/-- 概要：固定対象への全 compact 始域 slice の元の標準全余錐。
方針：全部分包含を元の対象上の全余錐として uncurry する。
規約：元の固定対象を保持する。
使われ方：compact filtered 生成表示の標準余錐。 -/
def compactSourceSliceDensityCocone (μ : Cardinal.{u})
    {C : SSet.{u + 1}} [Quasicategory C] (a : (Δ[0] : SSet.{u + 1}) ⟶ C) :
    JoinCocone ((fullSubcomplexOnVertices (sliceOver a)
      (fun v ↦ Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection a).app _ v))).ι ≫
        sliceOverProjection a) :=
  sliceDiagramCocone (fullSubcomplexOnVertices (sliceOver a)
    (fun v ↦ Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection a).app _ v))).ι

/-- 概要：全 compact 始域 slice の元の標準余錐は元の対象の余極限。
方針：全 compact 小模型を正確な Ind Yoneda 像として取り、標準左 Kan 密度を移す。
規約：元の圏と元の固定対象上の全余錐を結論する。
使われ方：点 fiber の小さい標準生成余錐の余極限性。 -/
lemma compactSourceSliceDensityCocone_isColimit {μ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (hC : IsKappaAccessible μ C)
    (hcol : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (a : (Δ[0] : SSet.{u + 1}) ⟶ C) :
    IsColimitCone (compactSourceSliceDensityCocone μ a) := by
  have : Fact μ.IsRegular := ⟨hC.1⟩
  obtain ⟨A, hA, ⟨a₀⟩⟩ := hC.exists_smallCompactModel
  have := hA
  obtain ⟨e, _, ⟨β⟩⟩ := hC.exists_compactModelIndRepresentation a₀
  obtain ⟨f, hf⟩ := exists_compactIndYonedaModel a₀ e β
  obtain ⟨y, rfl⟩ := SSet.yonedaEquiv.symm.surjective a
  have hc := indEquivalenceImage_canonicalColimits
    (show IsAccessible C from ⟨μ, hC⟩).isLocallySmall hcol e y
  rw [← hf] at hc
  apply (Ind.isColimitCone_iff_restrict_equivalentShape
    (compactSourceSliceKanComparison f y) (compactSourceSliceKanComparison_isQCatEquivalence f y)
    (compactSourceSliceDensityCocone μ (SSet.yonedaEquiv.symm y))).mpr
  apply (F2.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr hc
  change joinMap (compactSourceSliceKanComparison f y) (𝟙 Δ[0]) ≫
      sliceOverUncurry _ = sliceOverUncurry _ ≫ 𝟙 C
  rw [← sliceOverUncurry_precomp, compactSourceSliceKanComparison_inclusion, Category.comp_id]

end SerrePositivity.InfinityCategories.F2.Presentable
