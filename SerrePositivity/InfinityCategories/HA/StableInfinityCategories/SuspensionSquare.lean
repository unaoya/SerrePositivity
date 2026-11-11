module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport

/-! # Suspension と loop の四角形

概要：対角以外の二つの頂点が零対象である普遍四角形を構成する。
方針：X → 0 の cofiber と 0 → X の fiber を選ぶ。
規約：ここでは頂点と四角形を構成し、h C 上の関手性は別に証明する。
使われ方：S3 の suspension/loop 関手の対象部分。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 概要：正方形の下辺の始点は左下の頂点である。
方針：Yoneda と有限順序写像の計算を使う。
規約：第一座標は横方向。使われ方：cofiber の始点の識別。 -/
lemma squareBottomEdge_source {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    X.δ 1 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F)) = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0 := by
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, SSet.yonedaEquiv_comp]
  apply congrArg (fun s : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌ => F.app _ s)
  apply Prod.ext <;> decide

/-- 概要：正方形の下辺の終点は右下の頂点である。
方針：Yoneda と有限順序写像の計算を使う。
規約：第一座標は横方向。使われ方：cofiber の零角の識別。 -/
lemma squareBottomEdge_target {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    X.δ 0 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F)) = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 0 := by
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, SSet.yonedaEquiv_comp]
  apply congrArg (fun s : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌ => F.app _ s)
  apply Prod.ext <;> decide

/-- 概要：正方形の右辺の始点は右下の頂点である。
方針：Yoneda と有限順序写像の計算を使う。
規約：第一座標は横方向。使われ方：fiber の零角の識別。 -/
lemma squareRightEdge_source {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    X.δ 1 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F)) = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 0 := by
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, SSet.yonedaEquiv_comp]
  apply congrArg (fun s : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌ => F.app _ s)
  apply Prod.ext <;> decide

/-- 概要：正方形の右辺の終点は右上の頂点である。
方針：Yoneda と有限順序写像の計算を使う。
規約：第一座標は横方向。使われ方：fiber の終点の識別。 -/
lemma squareRightEdge_target {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    X.δ 0 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F)) = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 1 := by
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, SSet.yonedaEquiv_comp]
  apply congrArg (fun s : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌ => F.app _ s)
  apply Prod.ext <;> decide

/-- 概要：x の suspension 四角形は二つの零角を持つ押し出し四角形である。
方針：左下を x、対角以外を零にする。
規約：零頂点の特定の選択には固定しない。使われ方：suspension の対象部分。 -/
structure SuspensionSquare {X : SSet.{u}} (x : X _⦋0⦌) extends _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X where
  source_eq : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex square 0 0 = x
  other_zero : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex square 1 0)
  isPushout : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare square

/-- 概要：x の loop 四角形は二つの零角を持つ引き戻し四角形である。
方針：右上を x、対角以外を零にする。
規約：零頂点の特定の選択には固定しない。使われ方：loop の対象部分。 -/
structure LoopSquare {X : SSet.{u}} (x : X _⦋0⦌) extends _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X where
  target_eq : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex square 1 1 = x
  other_zero : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex square 1 0)
  isPullback : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare square

/-- 概要：suspension 四角形の右上の頂点。
方針：押し出しの頂点を取る。
規約：関手の対象部分の候補。使われ方：loop との比較。 -/
def SuspensionSquare.vertex {X : SSet.{u}} {x : X _⦋0⦌} (s : SuspensionSquare x) :
    X _⦋0⦌ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 1 1

/-- 概要：loop 四角形の左下の頂点。
方針：引き戻しの頂点を取る。
規約：関手の対象部分の候補。使われ方：suspension との比較。 -/
def LoopSquare.vertex {X : SSet.{u}} {x : X _⦋0⦌} (s : LoopSquare x) :
    X _⦋0⦌ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 0 0

/-- 概要：安定 ∞ 圏の任意の頂点は suspension 四角形を持つ。
方針：x → 0 の cofiber を取り、指定辺から両端の条件を読む。
規約：選択された零頂点を右下に使う。使われ方：suspension の選択。 -/
def chosenSuspensionSquare {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (x : X _⦋0⦌) : SuspensionSquare x := by
  let z := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X
  let f := Classical.choice (z.isTerminal.nonempty_edge x)
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare f
  have h (i : Fin 2) := congrArg
    (fun a : Δ[1] ⟶ X => X.δ i (SSet.yonedaEquiv a)) s.bottom_edge
  have hs : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 0 0 = x := by
    rw [← squareBottomEdge_source]
    exact (h 1).trans ((congrArg (fun a : X _⦋1⦌ => X.δ 1 a)
      ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).apply_symm_apply f.edge)).trans f.src_eq)
  have hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 1 0 = z.vertex := by
    rw [← squareBottomEdge_target]
    exact (h 0).trans ((congrArg (fun a : X _⦋1⦌ => X.δ 0 a)
      ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).apply_symm_apply f.edge)).trans f.tgt_eq)
  exact ⟨s.toZeroTriangle, hs, hz.symm ▸ z.isZero, s.isPushout⟩

/-- 概要：安定 ∞ 圏の任意の頂点は loop 四角形を持つ。
方針：0 → x の fiber を取り、指定辺から両端の条件を読む。
規約：選択された零頂点を右下に使う。使われ方：loop の選択。 -/
def chosenLoopSquare {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (x : X _⦋0⦌) : LoopSquare x := by
  let z := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X
  let f := Classical.choice (z.isInitial.nonempty_edge x)
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenFiberSquare f
  have h (i : Fin 2) := congrArg
    (fun a : Δ[1] ⟶ X => X.δ i (SSet.yonedaEquiv a)) s.right_edge
  have ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 1 1 = x := by
    rw [← squareRightEdge_target]
    exact (h 0).trans ((congrArg (fun a : X _⦋1⦌ => X.δ 0 a)
      ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).apply_symm_apply f.edge)).trans f.tgt_eq)
  have hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 1 0 = z.vertex := by
    rw [← squareRightEdge_source]
    exact (h 1).trans ((congrArg (fun a : X _⦋1⦌ => X.δ 1 a)
      ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).apply_symm_apply f.edge)).trans f.src_eq)
  exact ⟨s.toZeroTriangle, ht, hz.symm ▸ z.isZero, s.isPullback⟩

/-- 概要：安定 ∞ 圏の suspension 四角形は、その頂点の loop 四角形でもある。
方針：零角の押し出しから引き戻しへの安定性の判定を使う。
規約：元の四角形をそのまま使う。使われ方：ΣΩ の逆性の四角形。 -/
def SuspensionSquare.toLoopSquare {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x : X _⦋0⦌} (s : SuspensionSquare x) : LoopSquare s.vertex :=
  ⟨s.toZeroTriangle, rfl, s.other_zero,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout s.toZeroTriangle s.isPushout⟩

/-- 概要：安定 ∞ 圏の loop 四角形は、その頂点の suspension 四角形でもある。
方針：零角の引き戻しから押し出しへの安定性の判定を使う。
規約：元の四角形をそのまま使う。使われ方：ΣΩ の逆性の四角形。 -/
def LoopSquare.toSuspensionSquare {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x : X _⦋0⦌} (s : LoopSquare x) : SuspensionSquare s.vertex :=
  ⟨s.toZeroTriangle, rfl, s.other_zero,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback s.toZeroTriangle s.isPullback⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
