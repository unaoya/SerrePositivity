module

public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.LeftKanShapeIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenALeft

/-!
# 通常の comma の元の可縮性から nerve の余終性への接続

概要：元の comma 圏の終射の反転性から nerve の left cofinality を得る。
方針：F1b の comma と slice の実同型、弱可縮性の判定、Quillen A を使う。
規約：同じ宇宙の小圏で適用し、単体集合のモデル構造を要求しない。
使われ方：実際の分解の asphericity を右比較の余終性へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.FrameHom.NerveQuillenA

open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
open scoped Simplicial

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)

/-- 概要：全 comma の弱可縮性から nerve の left cofinality（Quillen A）。
方針：元の comma の弱可縮性を native な slice の引き戻しへ実同型で移す。
規約：標的の quasicategory 性は通常の nerve の実際の instance を使う。
使われ方：分解図式の全対象での余終性。 -/
lemma nerveMap_isLeftCofinal_of_weaklyContractible_comma
    (h : ∀ d : D, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (nerve (CostructuredArrow F d))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap F) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_weaklyContractible_slices
  intro b
  let d := b.obj 0
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex d = b := ComposableArrows.ext₀ rfl
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (nerveMap F) b)
  rw [← hb]
  let e := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso F d
  exact (AnodyneWeakDetection.isWeakHomotopyEquivalence e.hom
    (inferInstanceAs (IsIso (AnodyneHomotopy.anodyneQ.map e.hom)))).weaklyContractible_iff.mp
      (h d)

/-- 概要：全 comma の元の終射の反転性から nerve の left cofinality（Quillen A）。
方針：元の射の反転性から弱可縮性へ移して同じ slice 判定を使う。
規約：標的の quasicategory 性は通常の nerve の実際の instance を使う。
使われ方：分解図式の全対象での余終性。 -/
lemma nerveMap_isLeftCofinal
    (h : ∀ d : D, IsIso (AnodyneHomotopy.anodyneQ.map
      (SSet.stdSimplex.isTerminalObj₀.from (nerve (CostructuredArrow F d))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap F) :=
  nerveMap_isLeftCofinal_of_weaklyContractible_comma F
    (fun d => AnodyneWeakDetection.isWeaklyContractible _ (h d))

/-- 概要：余終な元の nerve の全 comma は弱可縮（Quillen A）。
方針：元の native な slice の必要条件を同じ comma の実同型で戻す。
規約：通常の comma 圏の全単体を扱う。
使われ方：全図式の comma の収縮先の弱可縮性。 -/
lemma comma_isWeaklyContractible (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap F)) (d : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (nerve (CostructuredArrow F d)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso F d
  exact (AnodyneWeakDetection.isWeakHomotopyEquivalence e.hom
    (inferInstanceAs (IsIso (AnodyneHomotopy.anodyneQ.map e.hom)))).weaklyContractible_iff.mpr
      (hF.slice_isWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex d))

end SerrePositivity.EInfinity.FrameHom.NerveQuillenA
