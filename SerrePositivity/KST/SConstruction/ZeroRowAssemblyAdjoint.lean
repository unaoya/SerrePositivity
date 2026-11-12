module
public import SerrePositivity.KST.SConstruction.AssemblyAdjointEvaluation
public import SerrePositivity.KST.SConstruction.ZeroRowLoopComparison
public import SerrePositivity.KST.SConstruction.SOneSlideBoundary
public import SerrePositivity.KST.SConstruction.SOneSlideAssembly
public import SerrePositivity.KST.SConstruction.CyclicBoundaryIso

/-! # 元の構造射の随伴と零行の具体的 loop 射の照合
概要：源の S₁ 交換と標的の巡回同型を介して、元の随伴を零行の loop 射と同定する。
方針：円の元の区間商上で評価し、元の assembly の交換式で比較する。
規約：元の区間の向きを保つ。使われ方：正の Ω 条件へ実際の構造射を接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial

/-- 元の標的の巡回同型を Kan 置換した後の、元の実現からの式。 -/
lemma iteratedRealizationToKan_cyclic (r : ℕ) (X : StableModel.{u}) :
    iteratedRealizationToKan r X ≫
      (Spectra.PointedKanReplacement.functor.map (cyclicBoundaryIso r X).hom).right =
      (iteratedSRealizationCyclicIso r X).hom ≫ boundaryReductionQuotient r X ≫
        (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization r X)).right := by
  have hn := congrArg (fun f => f.right)
    (Spectra.PointedKanReplacement.unit.naturality (cyclicBoundaryIso r X).hom)
  change (cyclicBoundaryIso r X).hom.right ≫
    (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization r X)).right =
      (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization r X)).right ≫
        (Spectra.PointedKanReplacement.functor.map (cyclicBoundaryIso r X).hom).right at hn
  simp only [iteratedRealizationToKan, Category.assoc]
  rw [← hn]
  have hc := congrArg (fun f => f ≫
    (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization r X)).right)
    (cyclicBoundaryIso_coordinate_quotient r X)
  simpa only [Category.assoc] using hc

/-- 元の構造射の随伴は、源の交換と標的の巡回補正を介して零行 loop 射と厳密に一致する。 -/
lemma zeroRowLoopComparison_assemblyAdjoint (r : ℕ) (X : StableModel.{u}) :
    (sOneInnerOuterRealizationIso (r + 1) X).hom ≫
      oneDirectionReductionQuotient r X ≫ ((kanTargetAssemblyAdjointNat r).app X).right =
      zeroRowLoopComparison (r + 1) X ≫
        ((PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map
          (Spectra.PointedKanReplacement.functor.map
            (cyclicBoundaryIso (r + 1) X).hom)).right := by
  apply loop_interval_hom_ext
  have hp := loop_interval_precomp
    ((boundaryKanRealizationFunctor (r + 1)).obj X)
    (sOneInnerOuterRealizationIso (r + 1) X).hom
    (oneDirectionReductionQuotient r X ≫ ((kanTargetAssemblyAdjointNat r).app X).right)
  rw [kanTargetAssemblyAdjoint_interval] at hp
  rw [hp]
  have hq := loop_interval_postcomp (zeroRowLoopComparison (r + 1) X)
    (Spectra.PointedKanReplacement.functor.map (cyclicBoundaryIso (r + 1) X).hom)
  rw [zeroRowLoopComparison_assembly] at hq
  refine Eq.trans ?_ hq.symm
  rw [← Category.assoc, sOneInnerOuterRealizationIso_assembly]
  simp only [Category.assoc]
  rw [iteratedRealizationToKan_cyclic]

/-- 源の元の境界商同型による同じ随伴の照合式。 -/
lemma zeroRowLoopComparison_reducedAssemblyAdjoint (r : ℕ) (X : StableModel.{u}) :
    boundaryReductionQuotient r (sStableModel 1 X) ≫
      (sOneInnerOuterReducedIso r X).hom.right ≫
        ((kanTargetAssemblyAdjointNat r).app X).right =
      zeroRowLoopComparison (r + 1) X ≫
        ((PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map
          (Spectra.PointedKanReplacement.functor.map
            (cyclicBoundaryIso (r + 1) X).hom)).right := by
  rw [← Category.assoc, sOneInnerOuterReducedIso_quotient, Category.assoc]
  exact zeroRowLoopComparison_assemblyAdjoint r X

/-- 元の全零境界商に降りた具体的 loop 比較。 -/
def zeroRowReducedLoopComparison (r : ℕ) (X : StableModel.{u}) :
    boundaryReducedRealization r (sStableModel 1 X) ⟶
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((boundaryKanRealizationFunctor (r + 1)).obj X) :=
  (sOneInnerOuterReducedIso r X).hom ≫ (kanTargetAssemblyAdjointNat r).app X ≫
    (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map
      (Spectra.PointedKanReplacement.functor.map (cyclicBoundaryIso (r + 1) X).inv)

/-- 元の全零境界商からの射を商射へ戻すと元の零行 loop 射を回収する。 -/
lemma zeroRowReducedLoopComparison_quotient (r : ℕ) (X : StableModel.{u}) :
    boundaryReductionQuotient r (sStableModel 1 X) ≫
      (zeroRowReducedLoopComparison r X).right = zeroRowLoopComparison (r + 1) X := by
  let L := PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}
  let T := Spectra.PointedKanReplacement.functor
  let e := cyclicBoundaryIso (r + 1) X
  have hi : (L.map (T.map e.hom)).right ≫ (L.map (T.map e.inv)).right = 𝟙 _ := by
    rw [← Under.comp_right, ← L.map_comp, ← T.map_comp, e.hom_inv_id,
      T.map_id, L.map_id]
    rfl
  have h := congrArg (fun f => f ≫ (L.map (T.map e.inv)).right)
    (zeroRowLoopComparison_reducedAssemblyAdjoint r X)
  change _ = (zeroRowLoopComparison (r + 1) X ≫
    (L.map (T.map e.hom)).right) ≫ (L.map (T.map e.inv)).right at h
  simp only [Category.assoc] at h
  rw [hi] at h
  exact h.trans (Category.comp_id _)

/-- 元の全零境界全体は具体的 loop 射で定数 loop に写る。 -/
lemma zeroRowLoopComparison_fatBoundary (r : ℕ) (X : StableModel.{u}) :
    (zeroDirectionsFatBoundary (r + 1) (sStableModel 1 X)).ι ≫
      zeroRowLoopComparison (r + 1) X =
      SemiCartesianMonoidalCategory.toUnit
        (zeroDirectionsFatBoundary (r + 1) (sStableModel 1 X)).toSSet ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((boundaryKanRealizationFunctor (r + 1)).obj X)).hom := by
  rw [← zeroRowReducedLoopComparison_quotient, ← Category.assoc]
  change ((zeroDirectionsFatBoundary (r + 1) (sStableModel 1 X)).ι ≫
    PointedObject.cofiberQuotient
      (zeroDirectionsFatBoundary (r + 1) (sStableModel 1 X)).ι) ≫ _ = _
  rw [PointedObject.cofiberQuotient_condition, Category.assoc, Under.w]

end SerrePositivity.KST.SConstruction
