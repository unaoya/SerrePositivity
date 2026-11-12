module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroCornerPasting
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberTriangle
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingComparisonHomotopy

/-! # 合成射の cofiber を比較する長方形

概要：cofiber 列の第一射に続く射を付加し、合成射の cofiber と元の cofiber を比較する。
方針：零角の押し出し長方形を構成し、左から外側への実際の変形を三角形の射へ移す。
規約：底辺二単体を厳密に保持する。使われ方：八面体の最初の三角形の射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Pretriangulated MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：指定 cofiber 列と合成二単体を保持した押し出し長方形。
方針：左面・底辺の等号と右面・外側の普遍性を保持する。
規約：右端を零対象に制限しない。使われ方：合成射の cofiber の同時構成。 -/
structure CofiberCompositionRectangle {X : SSet.{u}} (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X)
    (τ : (Δ[2] : SSet.{u}) ⟶ X) where
  diagram : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X
  left_eq : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare diagram 2 = t.square
  bottom_eq : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingBottomTriangle diagram = τ
  right_isPushout : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare diagram 0)
  outer_isPushout : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare diagram 1)

/-- 概要：適合する cofiber 列と合成二単体から比較長方形が存在する。
方針：零角の押し出し長方形の存在定理を使う。
規約：元の cofiber 性と第一辺の一致を仮定する。使われ方：八面体の最初の長方形。 -/
lemma nonempty_cofiberCompositionRectangle {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) (τ : (Δ[2] : SSet.{u}) ⟶ X)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square = stdSimplex.δ (2 : Fin 3) ≫ τ) :
    Nonempty (CofiberCompositionRectangle t τ) := by
  obtain ⟨F, hL, hB, hR, hO⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_pushoutRectangle_of_zeroTriangle t ht τ h
  exact ⟨⟨F, hL, hB, hR, hO⟩⟩

/-- 概要：合成射の cofiber を比較する長方形を一つ選ぶ。
方針：存在定理から選択する。
規約：第一辺の一致を入力する。使われ方：八面体の代表図式。 -/
def chosenCofiberCompositionRectangle {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) (τ : (Δ[2] : SSet.{u}) ⟶ X)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square = stdSimplex.δ (2 : Fin 3) ≫ τ) :
    CofiberCompositionRectangle t τ :=
  Classical.choice (nonempty_cofiberCompositionRectangle t ht τ h)

/-- 概要：長方形の外側は合成射の零角の列を与える。
方針：外側の左上は元の零角と同じ頂点である。
規約：外側の第一辺は指定二単体の長辺。使われ方：合成射の cofiber 三角形。 -/
def CofiberCompositionRectangle.outerZeroTriangle {X : SSet.{u}} {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (r : CofiberCompositionRectangle t τ) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X where
  square := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 1
  zero_corner := by
    have h : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 1) 0 1 =
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 2) 0 1 := rfl
    rw [h, r.left_eq]
    exact t.zero_corner

/-- 概要：合成射の外側の列は cofiber 列である。
方針：長方形に記録した外側の押し出し性を使う。
規約：指定長方形の入力後は追加仮定なし。使われ方：八面体の合成射の三角形。 -/
lemma CofiberCompositionRectangle.outer_isCofiber {X : SSet.{u}} {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (r : CofiberCompositionRectangle t τ) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence r.outerZeroTriangle := r.outer_isPushout

/-- 概要：元の列から合成射の列への実際の比較ホモトピー。
方針：長方形の左から外側への比較の先頭を左面の等号で輸送する。
規約：左列を全時間で保持する。使われ方：接続射と三角形の射の自然性。 -/
def CofiberCompositionRectangle.comparisonHomotopy {X : SSet.{u}} {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (r : CofiberCompositionRectangle t τ) :
    SSet.Homotopy t.square r.outerZeroTriangle.square where
  h := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy r.diagram).h
  h₀ := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy r.diagram).h₀.trans r.left_eq
  h₁ := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy r.diagram).h₁
  rel := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy r.diagram).rel

/-- 概要：比較ホモトピーは元の始点を固定する。
方針：左から外側への形状の固定条件に左面の等号を代入する。
規約：定値の道の厳密な等号。使われ方：第一成分が恒等であることの照合。 -/
lemma CofiberCompositionRectangle.comparisonHomotopy_source {X : SSet.{u}} {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (r : CofiberCompositionRectangle t τ) :
    ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      r.comparisonHomotopy.h = snd Δ[0] Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0) := by
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy_source r.diagram).trans
    (congrArg (fun R => snd (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0)) r.left_eq)

/-- 概要：元の cofiber 三角形から合成射の cofiber 三角形への射。
方針：実際の比較ホモトピーを接続射の自然性を含む三角形の射へ移す。
規約：安定性から得たシフトを使用する。使われ方：八面体の第一の三角形の射。 -/
def CofiberCompositionRectangle.triangleMorphism {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X} (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) {τ : (Δ[2] : SSet.{u}) ⟶ X}
    (r : CofiberCompositionRectangle t τ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle r.outerZeroTriangle r.outer_isCofiber :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangleMapOfHomotopy t r.outerZeroTriangle ht r.outer_isCofiber r.comparisonHomotopy

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
