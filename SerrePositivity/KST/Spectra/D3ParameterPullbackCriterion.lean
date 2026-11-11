module

public import SerrePositivity.KST.Spectra.D3BiParameterFaces
public import SerrePositivity.KST.Spectra.D3StrictPullbackSquare

/-!
概要：実パラメータ四角形の通常 pushout 性を、同じ全 Kan 入力図式の ∞ pullback 性へ移す。
方針：反変内部 Hom の極限保存と制限射の fibration 性を、元の二三角形へ接続する。
規約：パラメータ図式と実頂点を選び直さない。実二方向端点図式への代入は別葉で行う。
使われ方：テンソル後の端点四角形の内側の面を、元の全単体作用のまま極限認証する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3PullbackParameterSquareCategory : SmallCategory (Fin 2 × Fin 2) :=
  Preorder.smallCategory (Fin 2 × Fin 2)
local instance d3PullbackPointedCategory : SimplicialCategory PointedSimplicialSet.{u} :=
  PointedEnrichment.simplicialCategory

variable (D : (Fin 2 × Fin 2)ᵒᵖ ⥤ PointedSimplicialSet.{u})

/-- 元の逆向きパラメータ四角形が持つ通常の余極限性。 -/
abbrev D3ParameterIsPushout : Prop :=
  IsPushout
    (d3ParameterArrow D (show ((1, 0) : Fin 2 × Fin 2) ≤ (1, 1) by decide))
    (d3ParameterArrow D (show ((0, 1) : Fin 2 × Fin 2) ≤ (1, 1) by decide))
    (d3ParameterArrow D (show ((0, 0) : Fin 2 × Fin 2) ≤ (1, 0) by decide))
    (d3ParameterArrow D (show ((0, 0) : Fin 2 × Fin 2) ≤ (0, 1) by decide))

/-- 元の四つの制限射を同じ通常 Kan pullback 錐に束ねる。 -/
def d3ParameterPullbackCone (Y : PointedKanObject.{u}) :
    PullbackCone
      ((d3ParameterEvaluation D Y).map (homOfLE
        (show ((1, 0) : Fin 2 × Fin 2) ≤ (1, 1) by decide)))
      ((d3ParameterEvaluation D Y).map (homOfLE
        (show ((0, 1) : Fin 2 × Fin 2) ≤ (1, 1) by decide))) :=
  PullbackCone.mk
    ((d3ParameterEvaluation D Y).map (homOfLE
      (show ((0, 0) : Fin 2 × Fin 2) ≤ (1, 0) by decide)))
    ((d3ParameterEvaluation D Y).map (homOfLE
      (show ((0, 0) : Fin 2 × Fin 2) ≤ (0, 1) by decide))) (by
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1)

variable (hD : D3ParameterIsPushout D) (Y : PointedKanObject.{u})

include hD in
/-- 同じパラメータ pushout の反変内部 Hom は、元の実 Kan 錐の基礎極限。 -/
def d3ParameterPullbackCone_forget_isLimit :
    IsLimit (pointedKanProperty.ι.mapCone (d3ParameterPullbackCone D Y)) := by
  refine (isLimitMapConePullbackConeEquiv pointedKanProperty.ι
    (d3ParameterPullbackCone D Y).condition).symm ?_
  have hp : IsPullback (d3ParameterPullbackCone D Y).fst.hom
      (d3ParameterPullbackCone D Y).snd.hom
      (((d3ParameterEvaluation D Y).map (homOfLE
        (show ((1, 0) : Fin 2 × Fin 2) ≤ (1, 1) by decide))).hom)
      (((d3ParameterEvaluation D Y).map (homOfLE
        (show ((0, 1) : Fin 2 × Fin 2) ≤ (1, 1) by decide))).hom) := by
    apply IsPullback.of_map PointedSimplicialSet.forget
    · exact congrArg (fun f ↦ f.hom) (d3ParameterPullbackCone D Y).condition
    · have h := (hD.op.flip).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor Y.obj)
      change IsPullback
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
          (d3ParameterArrow D (show ((0, 0) : Fin 2 × Fin 2) ≤ (1, 0) by decide)) Y.obj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
          (d3ParameterArrow D (show ((0, 0) : Fin 2 × Fin 2) ≤ (0, 1) by decide)) Y.obj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
          (d3ParameterArrow D (show ((1, 0) : Fin 2 × Fin 2) ≤ (1, 1) by decide)) Y.obj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
          (d3ParameterArrow D (show ((0, 1) : Fin 2 × Fin 2) ≤ (1, 1) by decide)) Y.obj)
      simpa only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor_map] using h
  exact hp.isLimit

/-- 同じ実錐を元の Hom と同じ宇宙の cospan で保持する。 -/
def d3ParameterPullbackSmallCone :=
  (d3ParameterPullbackCone D Y).whisker
    (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan)

include hD in
/-- 元の通常極限は、同じ Kan 豊穣 Hom の極限も供給する。 -/
def d3ParameterPullbackSmallCone_hom_isLimit (Z : PointedKanObject.{u}) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (d3ParameterPullbackSmallCone D Y) Z) := by
  have hc : IsLimit (pointedKanProperty.ι.mapCone (d3ParameterPullbackSmallCone D Y)) :=
    (d3ParameterPullbackCone_forget_isLimit (D := D) (hD := hD) (Y := Y)).whiskerEquivalence
      (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm
  change IsLimit (((SimplicialCategory.sHomFunctor PointedKanObject.{u}).obj
    (Opposite.op Z)).mapCone (d3ParameterPullbackSmallCone D Y))
  rw [d3PointedKanHomFunctor]
  have hm := isLimitOfPreserves (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor Z.obj) hc
  exact IsLimit.ofIsoLimit hm (Functor.mapConeMapCone
    (H := pointedKanProperty.ι) (H' := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor Z.obj)
    (d3ParameterPullbackSmallCone D Y))

include hD in
/-- 元の制限射の fibration 性と全 Hom 極限性から、同じ実錐を ∞ 極限認証する。 -/
lemma d3ParameterPullbackSmallCone_isLimit
    [Mono (d3ParameterArrow D (show ((1, 0) : Fin 2 × Fin 2) ≤ (1, 1) by decide)).right] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (d3ParameterPullbackSmallCone D Y)) := by
  let f := (d3ParameterEvaluation D Y).map
    (homOfLE (show ((1, 0) : Fin 2 × Fin 2) ≤ (1, 1) by decide))
  let g := (d3ParameterEvaluation D Y).map
    (homOfLE (show ((0, 1) : Fin 2 × Fin 2) ≤ (1, 1) by decide))
  let a := d3ParameterArrow D (show ((1, 0) : Fin 2 × Fin 2) ≤ (1, 1) by decide)
  have : Mono a.right := inferInstance
  have : Fibration f.hom.right := by
    change Fibration (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Y.obj).right
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration a Y.obj
  have (Z : PointedKanObject.{u}) : Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (AsSmall.down ⋙ cospan f g) Z).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := by
    change Fibration (eHomWhiskerLeft SSet Z.obj f.hom)
    rw [PointedEnrichment.whiskerLeft_eq]
    exact PointedMapping.post_fibration Z.obj f.hom
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_homLimit (d3ParameterPullbackSmallCone D Y)
    (d3ParameterPullbackSmallCone_hom_isLimit (D := D) (hD := hD) (Y := Y))

/-- 同じ元の全パラメータ図式と実通常錐の二三角形を全単体で照合する。 -/
lemma d3ParameterSquare_eq_strict :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram ((d3PointedKanParameterSquare D).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y)) =
      D3StrictPullbackSquare.square (d3ParameterPullbackCone D Y) := by
  rw [d3PointedKanParameterSquare_vertex]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  · rw [D3StrictPullbackSquare.triangle_right]
    apply SSet.yonedaEquiv.injective
    rw [← Category.assoc, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent PointedKanObject).app _)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    refine ComposableArrows.ext₂ rfl rfl rfl ?_ ?_
    all_goals simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl
  · rw [D3StrictPullbackSquare.triangle_left]
    apply SSet.yonedaEquiv.injective
    rw [← Category.assoc, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent PointedKanObject).app _)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    refine ComposableArrows.ext₂ rfl rfl rfl ?_ ?_
    all_goals simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl

include hD in
/-- 元の全単体作用を持つパラメータ四角形を、同じ pushout から ∞ pullback 認証する。 -/
lemma d3ParameterSquare_isPullback
    [Mono (d3ParameterArrow D (show ((1, 0) : Fin 2 × Fin 2) ≤ (1, 1) by decide)).right] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram ((d3PointedKanParameterSquare D).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y))) := by
  rw [d3ParameterSquare_eq_strict]
  exact D3StrictPullbackSquare.isPullback _
    (d3ParameterPullbackSmallCone_isLimit (D := D) (hD := hD) (Y := Y))

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
