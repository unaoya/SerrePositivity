module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SymmetricSpan
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpecifiedCofiberSpan
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSameSpanSwap

/-! # 同じ零対象への同じ辺を使う suspension

概要：零対象へ向かう指定辺を二枝に使った suspension 四角形が存在する。
方針：指定した span の余極限を取り、四角形表示の二枝と三頂点を計算する。
規約：元の chosenSuspensionSquare は変更しない。使われ方：交換の span の等号を満たす模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：零対象への同じ辺を二枝に使った span は余極限を持つ。
方針：指定した終対象へ向かう第二枝の余極限存在を使う。
規約：辺と零対象を入力のまま保持する。使われ方：対称な suspension の余錐の選択。 -/
lemma hasColimit_edgeSpan_self {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x z : X _⦋0⦌} (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasColimit_span_of_terminal_second
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_right]
  have hv : stdSimplex.obj₀Equiv.symm (1 : Fin 2) =
      SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
    apply stdSimplex.ext
    intro i
    fin_cases i
    decide
  rw [hv, ← SSet.yonedaEquiv_comp]
  have ht := congrArg (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target f)
  simp only [Equiv.apply_symm_apply] at ht
  exact ht.symm ▸ hz.2

/-- 概要：指定した同じ零枝の span の余極限余錐を選ぶ。
方針：余極限の存在から古典的選択を使う。
規約：固定図式は edgeSpan f f のまま。使われ方：対称な suspension 四角形。 -/
def symmetricSuspensionCocone {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x z : X _⦋0⦌} (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) :=
  Classical.choose (hasColimit_edgeSpan_self f hz)

/-- 概要：選んだ対称な suspension の余錐は余極限である。
方針：余極限余錐の選択の仕様を読む。
規約：元の指定辺を固定する。使われ方：四角形の押し出し性。 -/
lemma symmetricSuspensionCocone_isColimit {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x z : X _⦋0⦌} (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (symmetricSuspensionCocone f hz) :=
  Classical.choose_spec (hasColimit_edgeSpan_self f hz)

/-- 概要：指定した零対象への辺を二枝に使う suspension 四角形。
方針：対称な span の余極限余錐を正方形へ戻し、二つの辺の端点を読む。
規約：安定性から存在を得るが、二枝の等号を厳密に保つ。使われ方：交換のループ表示。 -/
def symmetricSuspensionSquare {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x z : X _⦋0⦌} (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x := by
  let c := symmetricSuspensionCocone f hz
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare c = SSet.yonedaEquiv.symm f.edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_bottom, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_left]
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare c = SSet.yonedaEquiv.symm f.edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_left, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_right]
  have he := (SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).apply_symm_apply f.edge
  have hs : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare c) 0 0 = x := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source, hb]
    exact (congrArg (fun a : X _⦋1⦌ => X.δ 1 a) he).trans f.src_eq
  have h₁ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare c) 1 0 = z := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target, hb]
    exact (congrArg (fun a : X _⦋1⦌ => X.δ 0 a) he).trans f.tgt_eq
  have h₂ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare c) 0 1 = z := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target, hl]
    exact (congrArg (fun a : X _⦋1⦌ => X.δ 0 a) he).trans f.tgt_eq
  exact { square := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare c
          zero_corner := h₂.symm ▸ hz
          source_eq := hs
          other_zero := h₁.symm ▸ hz
          isPushout := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_isPushout c (symmetricSuspensionCocone_isColimit f hz) }

/-- 概要：対称な suspension の span は指定した辺を二度使う元の span。
方針：余錐から四角形への変換の span の計算則を使う。
規約：実際の図式の等号。使われ方：二枝交換に関する不変性。 -/
lemma symmetricSuspensionSquare_span {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x z : X _⦋0⦌} (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (symmetricSuspensionSquare f hz).square = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_span (symmetricSuspensionCocone f hz)

/-- 概要：対称な suspension の転置前後の span は等しい。
方針：転置の span の計算と同じ二枝の交換不変性を使う。
規約：条件付きの swapIso の比較に必要だった等号を証明する。
使われ方：交換作用を同じ coslice 内で読む。 -/
lemma symmetricSuspensionSquare_sameSpan {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x z : X _⦋0⦌} (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (symmetricSuspensionSquare f hz).transpose.square =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (symmetricSuspensionSquare f hz).square := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫
    (symmetricSuspensionSquare f hz).square) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutSpan_transpose, symmetricSuspensionSquare_span, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeSpan_self_swap]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
