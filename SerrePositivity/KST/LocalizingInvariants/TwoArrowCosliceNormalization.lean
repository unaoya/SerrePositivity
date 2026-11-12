module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceSpanAttachment

public import SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed
public import SerrePositivity.KST.LocalizingInvariants.CospanConeSquareLegs

/-!
概要：二本の元の実矢印と指定商四角形から、共通実始点と弱同値な実分母を回収する。
方針：同じ商四角形の coslice 図式へ実右分数 span を添付し、同じ有限全錐を回収する。
規約：元の二本の矢印と商四角形を全単体で保持し、共通始点・実分母を追加入力にしない。
使われ方：正次数の前段正規化で、二つの実四角形の共有辺を取り出す実有限台。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の二本の矢印を、同じ正方形の底辺と上辺へ含める。 -/
def twoArrowSquareBoundary : ((Δ[1] : SSet.{u}) ⨿ Δ[1]) ⟶ Δ[1] ⊗ Δ[1] :=
  coprod.desc _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge

lemma twoArrowSquareBoundary_left_vertex (v : Fin 2) :
    twoArrowSquareBoundary.{u}.app (Opposite.op ⦋0⦌)
      (((coprod.inl : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⨿ Δ[1])).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm v)) =
      (stdSimplex.obj₀Equiv.symm v, stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  change ((coprod.inl : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⨿ Δ[1]) ≫
    twoArrowSquareBoundary).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm v) = _
  rw [twoArrowSquareBoundary, coprod.inl_desc]
  rfl

lemma twoArrowSquareBoundary_right_vertex (v : Fin 2) :
    twoArrowSquareBoundary.{u}.app (Opposite.op ⦋0⦌)
      (((coprod.inr : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⨿ Δ[1])).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm v)) =
      (stdSimplex.obj₀Equiv.symm v, stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  change ((coprod.inr : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⨿ Δ[1]) ≫
    twoArrowSquareBoundary).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm v) = _
  rw [twoArrowSquareBoundary, coprod.inr_desc]
  rfl

def twoArrowFirstTarget : ((Δ[1] : SSet.{u}) ⨿ Δ[1]) _⦋0⦌ :=
  ((coprod.inl : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⨿ Δ[1])).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

def twoArrowSecondTarget : ((Δ[1] : SSet.{u}) ⨿ Δ[1]) _⦋0⦌ :=
  ((coprod.inr : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⨿ Δ[1])).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

def twoArrowSource : ((Δ[1] : SSet.{u}) ⨿ Δ[1]) _⦋0⦌ :=
  ((coprod.inl : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⨿ Δ[1])).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))

/-- 右分数 span 添付後の同じ元の最初の頂点。 -/
def twoArrowAttachedSource : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanAttachmentShape
    twoArrowFirstTarget.{u} twoArrowSecondTarget) _⦋0⦌ :=
  (pushout.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionDiagramTargets twoArrowFirstTarget.{u} twoArrowSecondTarget.{u})
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanTargets.{u}).app (Opposite.op ⦋0⦌) twoArrowSource

/-- 元の商四角形の同じ coslice 図式を、二本の元の矢印へ制限する。 -/
def twoArrowCosliceDiagram {X : SSet.{u}} {F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed F) : ((Δ[1] : SSet.{u}) ⨿ Δ[1]) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint F) := twoArrowSquareBoundary ≫ s.lift

lemma twoArrowCoslice_first_target {X : SSet.{u}} {F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed F) :
    (twoArrowCosliceDiagram s).app (Opposite.op ⦋0⦌) twoArrowFirstTarget =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.lift 1 0 := by
  change s.lift.app (Opposite.op ⦋0⦌)
    (twoArrowSquareBoundary.app (Opposite.op ⦋0⦌) twoArrowFirstTarget) = _
  rw [twoArrowFirstTarget, twoArrowSquareBoundary_left_vertex]
  rfl

lemma twoArrowCoslice_second_target {X : SSet.{u}} {F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed F) :
    (twoArrowCosliceDiagram s).app (Opposite.op ⦋0⦌) twoArrowSecondTarget =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.lift 1 1 := by
  change s.lift.app (Opposite.op ⦋0⦌)
    (twoArrowSquareBoundary.app (Opposite.op ⦋0⦌) twoArrowSecondTarget) = _
  rw [twoArrowSecondTarget, twoArrowSquareBoundary_right_vertex]
  rfl

/-- 同じ指定商四角形の後辺を、元の二頂点を持つ同じ実 coslice 辺にする。 -/
def twoArrowCosliceEdge {X : SSet.{u}} {F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed F) :
    Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint F)))
      ((twoArrowCosliceDiagram s).app (Opposite.op ⦋0⦌) twoArrowFirstTarget)
      ((twoArrowCosliceDiagram s).app (Opposite.op ⦋0⦌) twoArrowSecondTarget) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow s.lift).edge,
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow s.lift).src_eq.trans (twoArrowCoslice_first_target s).symm,
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow s.lift).tgt_eq.trans (twoArrowCoslice_second_target s).symm⟩

lemma twoArrowCoslice_projection {B C : SSet.{u}} (q : B ⟶ C)
    (D L : (Δ[1] : SSet.{u}) ⟶ B) (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed F) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F = D ≫ q)
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ F = L ≫ q) :
    twoArrowCosliceDiagram s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint F) =
      coprod.desc D L ≫ q := by
  rw [twoArrowCosliceDiagram, Category.assoc, s.projection]
  apply coprod.hom_ext
  · simpa only [← Category.assoc, twoArrowSquareBoundary, coprod.inl_desc] using hb
  · simpa only [← Category.assoc, twoArrowSquareBoundary, coprod.inr_desc] using ht

/-- 同じ元の左下頂点への実商錐の脚は可逆。 -/
lemma twoArrowCoslice_initial_invertible {B C : SSet.{u}} (q : B ⟶ C)
    (D L : (Δ[1] : SSet.{u}) ⟶ B) (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed F) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F = D ≫ q)
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ F = L ≫ q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := C) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg
      (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (twoArrowCosliceDiagram s),
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection _).trans
          (twoArrowCoslice_projection q D L F s hb ht)⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (coprod.desc D L ≫ q))
      twoArrowSource) := by
  let c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry s.lift,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection s.lift).trans s.projection⟩
  let d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (coprod.desc D L ≫ q) := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (twoArrowCosliceDiagram s),
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection _).trans (twoArrowCoslice_projection q D L F s hb ht)⟩
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) twoArrowSquareBoundary ≫ c.val = d.val := by
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp s.lift twoArrowSquareBoundary).symm
  have he := nativeConeLeg_restriction c d twoArrowSquareBoundary hc twoArrowSource
  have hv : twoArrowSquareBoundary.app (Opposite.op ⦋0⦌) twoArrowSource =
      _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquareInitialVertex := twoArrowSquareBoundary_left_vertex 0
  rw [hv] at he
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mp s.initial_isInvertible

/-- 元の二本の矢印と商四角形から、同じ有限全錐・共有始点・元の始点への実分母を回収する。 -/
lemma exists_verdierTwoArrowCosliceNormalization {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (D L : (Δ[1] : SSet.{u}) ⟶ B.obj)
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F = D ≫ q.hom) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ F = L ≫ q.hom) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.SquareCosliceSeed F,
      let p := coprod.desc D L
      let U := twoArrowCosliceDiagram s
      let hU := twoArrowCoslice_projection q.hom D L F s hb ht
      ∃ r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization h (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.fractionSquarePoint F)
          (twoArrowCosliceEdge s) (p.app (Opposite.op ⦋0⦌) twoArrowFirstTarget)
          (p.app (Opposite.op ⦋0⦌) twoArrowSecondTarget),
        ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanNativeDiagram p U twoArrowFirstTarget twoArrowSecondTarget r),
          Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanNativeDiagram p U twoArrowFirstTarget twoArrowSecondTarget r ≫ q.hom))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom c)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanQuotientCone p U twoArrowFirstTarget twoArrowSecondTarget r hU)) ∧
          ∃ s₀ : Truncated.Edge (X := (truncation 2).obj B.obj) c.vertex
              (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))),
            s₀.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c twoArrowAttachedSource).edge ∧
            s₀.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  obtain ⟨s⟩ := _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.exists_squareCosliceSeed F
  refine ⟨s, ?_⟩
  let p := coprod.desc D L
  let U := twoArrowCosliceDiagram s
  have hU := twoArrowCoslice_projection q.hom D L F s hb ht
  obtain ⟨r, c, e, hw⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierFiniteCosliceSpanAttachment
    (h := h) p U twoArrowFirstTarget twoArrowSecondTarget (e := twoArrowCosliceEdge s) hU
  let c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (p ≫ q.hom) := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry U,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection U).trans hU⟩
  let t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanQuotientCone p U twoArrowFirstTarget twoArrowSecondTarget r hU
  let j : ((Δ[1] : SSet.{u}) ⨿ Δ[1]) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanAttachmentShape twoArrowFirstTarget.{u} twoArrowSecondTarget := pushout.inl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionDiagramTargets twoArrowFirstTarget.{u} twoArrowSecondTarget.{u})
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSpanTargets.{u}
  have he := nativeConeLeg_restriction t c₀ j
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanQuotientCone_original p U twoArrowFirstTarget twoArrowSecondTarget r hU)
    twoArrowSource
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := C.obj) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg t twoArrowAttachedSource) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr (twoArrowCoslice_initial_invertible q.hom D L F s hb ht)
  have hW := hw twoArrowAttachedSource hi
  have hv : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanNativeDiagram p U twoArrowFirstTarget twoArrowSecondTarget r).app
      (Opposite.op ⦋0⦌) twoArrowAttachedSource =
      D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    have hp := congrArg (fun f : ((Δ[1] : SSet.{u}) ⨿ Δ[1]) ⟶ B.obj =>
      f.app (Opposite.op ⦋0⦌) twoArrowSource)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cosliceSpanNativeDiagram_original p U twoArrowFirstTarget twoArrowSecondTarget r)
    have hp₀ : p.app (Opposite.op ⦋0⦌) twoArrowSource =
        D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
      change ((coprod.inl : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⨿ Δ[1]) ≫ p).app
        (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = _
      rw [coprod.inl_desc]
    exact hp.trans hp₀
  let s₀ : Truncated.Edge (X := (truncation 2).obj B.obj) c.vertex
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) :=
    ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c twoArrowAttachedSource).edge,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c twoArrowAttachedSource).src_eq,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c twoArrowAttachedSource).tgt_eq.trans hv⟩
  exact ⟨r, c, ⟨e⟩, s₀, rfl, hW⟩

end SerrePositivity.KST.LocalizingInvariants
