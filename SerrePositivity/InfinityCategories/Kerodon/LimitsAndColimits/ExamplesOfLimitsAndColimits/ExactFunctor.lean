module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PushoutCofiberRectangle
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Bicartesian

/-! # 安定 ∞ 圏の完全関手

概要：零対象と cofiber 列を保つ単体的関手を定義する。
方針：安定性で fiber 列の保存を導き、零終点の長方形と貼り合わせで全四角形へ拡張する。
規約：完全性の定義に任意の押し出し・引き戻しの保存は仮定しない。
使われ方：S6 の懸垂比較とホモトピー圏の三角関手。

対応節は Kerodon 7.6（Tag 03E8）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits

/-- 概要：単体的関手が零頂点を保つという条件。
方針：全ての零頂点の像の零性を要求する。
規約：始終対象の選択には依存しない。使われ方：零角の図式の後合成。 -/
def PreservesZeroVertices {X Y : SSet.{u}} (F : X ⟶ Y) : Prop :=
  ∀ (x : X _⦋0⦌), _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex x → _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x)

/-- 概要：零頂点を保つ関手で零角の四角形を写す。
方針：四角形を後合成し、零角の証明を写す。
規約：角の位置を変えない。使われ方：fiber/cofiber 列の保存。 -/
def ZeroTriangle.map {X Y : SSet.{u}} (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (F : X ⟶ Y)
    (hF : PreservesZeroVertices F) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle Y where
  square := t.square ≫ F
  zero_corner := hF _ t.zero_corner

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ZeroTriangle (map)


/-- 概要：完全関手は零頂点と cofiber 列を保つ。
方針：二つの保存条件を命題としてまとめる。
規約：fiber 列の保存は安定性から導く。使われ方：完全関手の合成と三角構造。 -/
class IsExactFunctor {X Y : SSet.{u}} (F : X ⟶ Y) : Prop where
  preservesZero : PreservesZeroVertices F
  preservesCofiber (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t → _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence (t.map F preservesZero)

/-- 概要：恒等関手は完全。
方針：零頂点と列をそのまま保つ。
規約：値域に安定性は不要。使われ方：完全関手の恒等射。 -/
instance isExactFunctor_id (X : SSet.{u}) : IsExactFunctor (𝟙 X) where
  preservesZero _ h := h
  preservesCofiber _ h := h

/-- 概要：完全関手の合成は完全。
方針：零性と cofiber 性の保存を順に適用する。
規約：単体的な合成。使われ方：完全関手の圏。 -/
instance isExactFunctor_comp {X Y Z : SSet.{u}} (F : X ⟶ Y) (G : Y ⟶ Z)
    [IsExactFunctor F] [IsExactFunctor G] : IsExactFunctor (F ≫ G) where
  preservesZero x h := IsExactFunctor.preservesZero (F := G) _ (IsExactFunctor.preservesZero (F := F) x h)
  preservesCofiber t h :=
    IsExactFunctor.preservesCofiber (F := G) (t.map F (IsExactFunctor.preservesZero (F := F)))
      (IsExactFunctor.preservesCofiber (F := F) t h)

/-- 概要：安定 ∞ 圏間の完全関手は fiber 列も保つ。
方針：始域と終域の fiber/cofiber 判定を使う。
規約：追加の保存条件は不要。使われ方：完全性の双対表示。 -/
lemma IsExactFunctor.preservesFiber {X Y : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y] (F : X ⟶ Y) [IsExactFunctor F]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (h : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence (t.map F (IsExactFunctor.preservesZero (F := F))) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout _
    (IsExactFunctor.preservesCofiber (F := F) t (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback t h))

/-- 概要：零頂点と fiber 列を保つ関手は完全。
方針：安定性で cofiber 列を fiber 列へ移して保存する。
規約：始域と終域は安定な quasicategory。使われ方：完全性の対称な判定。 -/
lemma isExactFunctor_of_preservesFiber {X Y : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y] (F : X ⟶ Y) (hF : PreservesZeroVertices F)
    (h : ∀ t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t → _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence (t.map F hF)) :
    IsExactFunctor F where
  preservesZero := hF
  preservesCofiber t ht :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback _ (h t (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout t ht))

/-- 概要：完全関手は任意の押し出し四角形を保つ。
方針：右下に零対象を付加する。外側と右面の転置は cofiber 列なので像も普遍的であり、
引き戻しの貼り合わせの消去から像の左面を復元する。
規約：元の四角形に零角は不要。使われ方：完全関手の有限図式の保存。 -/
lemma IsExactFunctor.preservesPushoutSquare {X Y : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (F : X ⟶ Y) [IsExactFunctor F] (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare L) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (L ≫ F) := by
  let r := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenPushoutCofiberRectangle L hL
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (r.diagram ≫ F) 0) := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose _).2
    exact IsExactFunctor.preservesCofiber (F := F) r.rightZeroTriangle r.right_isCofiber
  have ho : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (r.diagram ≫ F) 1) := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose _).2
    exact IsExactFunctor.preservesCofiber (F := F) r.outerZeroTriangle r.outer_isCofiber
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isPullbackSquare_pasting_cancel_right (r.diagram ≫ F)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout_square _ hr)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout_square _ ho)
  have hp := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback_square _ hl
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 2 ≫ F) at hp
  rwa [r.left_eq] at hp

/-- 概要：完全関手は任意の引き戻し四角形を保つ。
方針：両安定 ∞ 圏で押し出しと引き戻しが一致することを使う。
規約：零角は不要。使われ方：完全関手の極限側の特徴づけ。 -/
lemma IsExactFunctor.preservesPullbackSquare {X Y : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (F : X ⟶ Y) [IsExactFunctor F] (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare L) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (L ≫ F) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout_square _
    (IsExactFunctor.preservesPushoutSquare F L (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback_square L hL))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
