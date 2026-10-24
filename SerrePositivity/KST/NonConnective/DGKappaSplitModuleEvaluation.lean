module
public import SerrePositivity.KST.NonConnective.DGKappaSplitPerfEvaluation
public import SerrePositivity.DifferentialGraded.Module.ConeDesc
public import SerrePositivity.InfinityCategories.Derived.FullColimitReflection

/-!
概要：元の各 Perf ラベルの分裂を、同じ実右 dg 加群の cone へ接続する。
方針：ラベル評価と充満包含で指定閉射を送り、元の零合成の cone 延長を取る。
規約：全次数 Hom を保持し、右逆だけから cofiber 性を結論しない。
使われ方：点ごとの分裂四角形の cofiber 普遍性の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (X : PresentedPerfectDGObject R (DGKappaCone R D I))

/-- 元のラベル作用を、同じ全 Hom を持つ実右 dg 加群へ評価する。 -/
def dgKappaModuleLabelAction :=
  (presentedPerfectDGLabelAction R (DGKappaCone R D I) (DGKappaCone R D I) X).comp
    ((presentedPerfectDGEvaluation R (DGKappaCone R D I)).comp
      (perfectDGModuleInclusion R (DGKappaCone R D I) Set.univ))

/-- 同じ閉注入と右射影の実加群での零合成。 -/
theorem dgKappaSplitModule_head_tail :
    (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitHead R D I) ≫
        (dgKappaModuleLabelAction R D I X).onClosed.map
          (dgKappaSplitTailProjection R D I) = 0 := by
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] using
    congrArg (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplit_head_tail R D I)

/-- 元の閉注入の標準 cone から、同じ元の右射影を延長した実加群射。 -/
def dgKappaSplitModuleConeProjection :=
  moduleConeDesc R (DGKappaCone R D I)
    ((dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitHead R D I))
    ((dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitTailProjection R D I))
    (dgKappaSplitModule_head_tail R D I X)

/-- 元の右注入による、同じ cone 射影の具体的切断。 -/
def dgKappaSplitModuleConeSection :=
  (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitTail R D I) ≫
    moduleConeInr R (DGKappaCone R D I)
      ((dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitHead R D I))

/-- この実 cone 射影と切断は、右側で厳密に恒等へ合成する。 -/
theorem dgKappaSplitModuleConeSection_projection :
    dgKappaSplitModuleConeSection R D I X ≫
        dgKappaSplitModuleConeProjection R D I X = 𝟙 _ := by
  dsimp only [dgKappaSplitModuleConeSection, dgKappaSplitModuleConeProjection]
  rw [Category.assoc, moduleConeDesc_inr, ← CategoryTheory.Functor.map_comp,
    dgKappaSplit_tail_tail, CategoryTheory.Functor.map_id]

/-- 同じ点ごとの四角形の全右 dg 加群像の cofiber 性から、元の Perf での性質を反映する。 -/
theorem dgKappaSplitPerfPointwiseSquare_isPushout_of_module
    (Z : DGKappaZeroInput R D I)
    (h : IsPushoutSquare ((dgKappaSplitPerfPointwiseSquare R D I X Z ≫
        dgNerve.map (presentedPerfectDGEvaluation R (DGKappaCone R D I))) ≫
      dgNerve.map (perfectDGModuleInclusion R (DGKappaCone R D I) Set.univ))) :
    IsPushoutSquare (dgKappaSplitPerfPointwiseSquare R D I X Z) := by
  apply (dgKappaSplitPerfPointwiseSquare_isPushout_iff_evaluation R D I X Z).mpr
  apply DGNerve.isColimitCone_of_fullInclusion R (RightModule R (DGKappaCone R D I))
    (modulePerfectProjectiveOver R (DGKappaCone R D I) Set.univ) (pushoutCocone _)
  exact h

end SerrePositivity.KST.NonConnective
