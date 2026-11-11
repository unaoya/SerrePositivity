module
public import SerrePositivity.KST.NonConnective.DGKappaSplitPerfEvaluation
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullColimitReflection

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

private lemma closedLabelNerve_comp {R : Type u} [CommRing R]
    {A B C E : Type v} [DGCategory R A] [DGCategory R B]
    [DGCategory R C] [DGCategory R E]
    (F : DGFunctor R A B) (G : DGFunctor R B C) (H : DGFunctor R C E) :
    nerveMap F.onClosed ≫ nerveMap G.onClosed ≫ nerveMap H.onClosed =
      nerveMap (F.comp (G.comp H)).onClosed := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  rfl

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (X : PresentedPerfectDGObject R (DGKappaCone R D I))

/-- 元のラベル作用を、同じ全 Hom を持つ実右 dg 加群へ評価する。 -/
def dgKappaModuleLabelAction :=
  (presentedPerfectDGLabelAction R (DGKappaCone R D I) (DGKappaCone R D I) X).comp
    ((presentedPerfectDGEvaluation R (DGKappaCone R D I)).comp
      (perfectDGModuleInclusion R (DGKappaCone R D I) Set.univ))

/-- 元の点ごとの全四角形を、そのまま実右 dg 加群へ送る。 -/
def dgKappaSplitModuleSquare (Z : DGKappaZeroInput R D I) :=
  (dgKappaSplitPerfPointwiseSquare R D I X Z ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation R (DGKappaCone R D I))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R (DGKappaCone R D I) Set.univ)

/-- 上下二胞体を含む実加群四角形は、同じ元の閉分裂四角形のラベル作用像に等しい。 -/
theorem dgKappaSplitModuleSquare_closed (Z : DGKappaZeroInput R D I) :
    dgKappaSplitModuleSquare R D I X Z =
      dgKappaSplitClosedSquare R D I Z ≫
        nerveMap (dgKappaModuleLabelAction R D I X).onClosed ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveInclusion R (RightModule R (DGKappaCone R D I)) := by
  dsimp only [dgKappaSplitModuleSquare]
  rw [dgKappaSplitPerfPointwiseSquare_closed]
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveInclusion_dgFunctor]
  have hc := closedLabelNerve_comp
    (presentedPerfectDGLabelAction R (DGKappaCone R D I) (DGKappaCone R D I) X)
    (presentedPerfectDGEvaluation R (DGKappaCone R D I))
    (perfectDGModuleInclusion R (DGKappaCone R D I) Set.univ)
  simpa only [Category.assoc, dgKappaPerfLabelFunctor, dgKappaModuleLabelAction] using
    congrArg (fun m => dgKappaSplitClosedSquare R D I Z ≫ m ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveInclusion R (RightModule R (DGKappaCone R D I))) hc

/-- 同じ閉注入と右射影の実加群での零合成。 -/
theorem dgKappaSplitModule_head_tail :
    (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitHead R D I) ≫
        (dgKappaModuleLabelAction R D I X).onClosed.map
          (dgKappaSplitTailProjection R D I) = 0 := by
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] using
    congrArg (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplit_head_tail R D I)

/-- 実加群の同じ左注入と左射影は厳密に分裂する。 -/
theorem dgKappaSplitModule_head_head :
    (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitHead R D I) ≫
        (dgKappaModuleLabelAction R D I X).onClosed.map
          (dgKappaSplitHeadProjection R D I) = 𝟙 _ := by
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
    congrArg (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplit_head_head R D I)

/-- 実加群の同じ右注入と左射影の交差合成は零。 -/
theorem dgKappaSplitModule_tail_head :
    (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitTail R D I) ≫
        (dgKappaModuleLabelAction R D I X).onClosed.map
          (dgKappaSplitHeadProjection R D I) = 0 := by
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] using
    congrArg (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplit_tail_head R D I)

/-- 実加群の同じ右注入と右射影は厳密に分裂する。 -/
theorem dgKappaSplitModule_tail_tail :
    (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitTail R D I) ≫
        (dgKappaModuleLabelAction R D I X).onClosed.map
          (dgKappaSplitTailProjection R D I) = 𝟙 _ := by
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
    congrArg (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplit_tail_tail R D I)

/-- 元の恒等分解は、同じ実加群作用の全 Hom 上で保持される。 -/
theorem dgKappaSplitModule_decomposition :
    (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitHeadProjection R D I) ≫
        (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitHead R D I) +
      (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitTailProjection R D I) ≫
        (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitTail R D I) = 𝟙 _ := by
  simpa only [CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_id] using
      congrArg (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplit_decomposition R D I)

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
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((dgKappaSplitPerfPointwiseSquare R D I X Z ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation R (DGKappaCone R D I))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R (DGKappaCone R D I) Set.univ))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgKappaSplitPerfPointwiseSquare R D I X Z) := by
  apply (dgKappaSplitPerfPointwiseSquare_isPushout_iff_evaluation R D I X Z).mpr
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isColimitCone_of_fullInclusion R (RightModule R (DGKappaCone R D I))
    (modulePerfectProjectiveOver R (DGKappaCone R D I) Set.univ) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone _)
  exact h

end SerrePositivity.KST.NonConnective
