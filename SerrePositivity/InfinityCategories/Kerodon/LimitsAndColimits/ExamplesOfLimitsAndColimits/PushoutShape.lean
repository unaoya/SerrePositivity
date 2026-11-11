module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinLeftColimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import Mathlib.Tactic.CrossRefAttribute

/-! # span の余錐と正方形

概要：Λ[2,0]⋆Δ[0] を正方形と同定し、押し出し四角形を余極限として扱う。
方針：二つの三角形の対角に沿う pushout を比較する。
規約：span は (0,0) から (1,0) と (0,1)、余錐頂点は (1,1)。
使われ方：HA §1.1 の cofiber 四角形の具体的な join 表示。

対応節は Kerodon 7.6（Tag 03E8）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
open CategoryTheory Limits MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 概要：span の第一の辺と余錐頂点の三角形。
方針：辺と点の join を使う。
規約：span の辺は 0→1。使われ方：押し出しの第一三角形。 -/
def spanCoconeTriangleLeft : (Δ[2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (horn 2 0 : SSet.{u}) Δ[0] :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap horn₂₀.ι₀₁ (𝟙 Δ[0])

/-- 概要：span の第二の辺と余錐頂点の三角形。
方針：辺と点の join を使う。
規約：span の辺は 0→2。使われ方：押し出しの第二三角形。 -/
def spanCoconeTriangleRight : (Δ[2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (horn 2 0 : SSet.{u}) Δ[0] :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap horn₂₀.ι₀₂ (𝟙 Δ[0])

/-- 概要：辺の始点と余錐頂点を結ぶ共通辺は三角形の対角の面。
方針：join の標準単体同型で有限頂点写像を計算する。
規約：共通辺は δ₁。使われ方：二三角形の貼り合わせ。 -/
lemma spanCocone_gluing :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 (Δ[0] : SSet.{u})) =
      stdSimplex.δ (1 : Fin 3) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：span の余錐は対角に沿う二つの三角形の pushout。
方針：ホーンの pushout を右因子固定の join 関手で送り、標準単体同型で移す。
規約：単体集合の通常の pushout の計算。使われ方：余錐と正方形の同型。 -/
lemma spanCocone_isPushout : IsPushout (stdSimplex.δ (1 : Fin 3)) (stdSimplex.δ (1 : Fin 3))
    spanCoconeTriangleLeft.{u} spanCoconeTriangleRight := by
  apply (horn₂₀.isPushout.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftFunctor (Δ[0] : SSet.{u}))).of_iso'
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).symm (Iso.refl _)
  · exact spanCocone_gluing
  · exact spanCocone_gluing
  · rfl
  · rfl

/-- 概要：span の余錐は正方形と同型である。
方針：二三角形の pushout の普遍性を比較する。
規約：左三角形は正方形の番号 1、右三角形は番号 0。使われ方：押し出しの余錐表示。 -/
def spanCoconeSquareIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (horn 2 0 : SSet.{u}) (Δ[0] : SSet.{u}) ≅ Δ[1] ⊗ Δ[1] :=
  spanCocone_isPushout.isoIsPushout _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.flip

/-- 概要：第一余錐三角形は正方形の下側の三角形となる。
方針：pushout の比較同型の第一包含の式を使う。
規約：三角形番号 1。使われ方：span の辺の計算。 -/
lemma spanCoconeSquareIso_left :
    spanCoconeTriangleLeft ≫ spanCoconeSquareIso.{u}.hom = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 :=
  spanCocone_isPushout.inl_isoIsPushout_hom _ _ _

/-- 概要：第二余錐三角形は正方形の上側の三角形となる。
方針：pushout の比較同型の第二包含の式を使う。
規約：三角形番号 0。使われ方：span の辺の計算。 -/
lemma spanCoconeSquareIso_right :
    spanCoconeTriangleRight ≫ spanCoconeSquareIso.{u}.hom = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 :=
  spanCocone_isPushout.inr_isoIsPushout_hom _ _ _

/-- 概要：正方形の第一の始点側の辺。
方針：第一座標を恒等、第二座標を始点とする。
規約：(0,0)→(1,0)。使われ方：cofiber を取る射。 -/
def squareBottomEdge : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  CartesianMonoidalCategory.lift (𝟙 Δ[1]) (SSet.const (stdSimplex.obj₀Equiv.symm 0))

/-- 概要：正方形の第二の始点側の辺。
方針：第一座標を始点、第二座標を恒等とする。
規約：(0,0)→(0,1)。使われ方：零頂点への射。 -/
def squareLeftEdge : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  CartesianMonoidalCategory.lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 Δ[1])

/-- 概要：span の正方形への包含。
方針：余錐の左包含を正方形の同型で送る。
規約：始点側の二辺。使われ方：押し出しの固定図式。 -/
def spanSquareBoundary : (horn 2 0 : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (horn 2 0 : SSet.{u}) Δ[0] ≫ spanCoconeSquareIso.hom

/-- 概要：四角形の始点側の二辺の span。
方針：span の包含で制限する。
規約：Λ[2,0] の向き。使われ方：押し出し余錐の図式。 -/
def pushoutSpan {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    (horn 2 0 : SSet.{u}) ⟶ X := spanSquareBoundary ≫ F

/-- 概要：四角形をその span の余錐に直す。
方針：span の余錐と正方形の同型で前合成する。
規約：図式は左因子で固定。使われ方：押し出しの余極限性。 -/
def pushoutCocone {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (pushoutSpan F) :=
  ⟨spanCoconeSquareIso.hom ≫ F, by
    simp only [pushoutSpan, spanSquareBoundary, Category.assoc]⟩

/-- 概要：押し出し四角形はその span の余極限余錐である。
方針：coslice の始対象による余極限性を適用する。
規約：h C の通常の押し出しではない。使われ方：HA §1.1 の cofiber 列。 -/
@[kerodon 03FF]
def IsPushoutSquare {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (pushoutCocone F)

/-- 概要：辺と点の join の左包含は三角形の最初の辺。
方針：標準単体同型を有限頂点写像で計算する。
規約：面は δ₂。使われ方：span の辺の同定。 -/
lemma joinStdSimplexIso_one_zero_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u}) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom = stdSimplex.δ 2 := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：span の第一の辺は正方形の (0,0)→(1,0)。
方針：余錐の第一三角形を最初の辺に制限する。
規約：span の辺は 0→1。使われ方：cofiber の入力の向きの確認。 -/
lemma spanSquareBoundary_bottomEdge :
    horn₂₀.ι₀₁ ≫ spanSquareBoundary.{u} = squareBottomEdge := by
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[1] Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap horn₂₀.ι₀₁ (𝟙 Δ[0]) ≫
        spanCoconeSquareIso.hom) := by
      simp only [spanSquareBoundary, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap]
    _ = stdSimplex.δ (2 : Fin 3) ≫
        (spanCoconeTriangleLeft ≫ spanCoconeSquareIso.hom) := by
      rw [← joinStdSimplexIso_one_zero_inl]
      simp only [spanCoconeTriangleLeft, Category.assoc, Iso.hom_inv_id_assoc]
    _ = squareBottomEdge := by
      rw [spanCoconeSquareIso_left]
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide

/-- 概要：span の第二の辺は正方形の (0,0)→(0,1)。
方針：余錐の第二三角形を最初の辺に制限する。
規約：span の辺は 0→2。使われ方：零頂点への射の向きの確認。 -/
lemma spanSquareBoundary_leftEdge :
    horn₂₀.ι₀₂ ≫ spanSquareBoundary.{u} = squareLeftEdge := by
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[1] Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap horn₂₀.ι₀₂ (𝟙 Δ[0]) ≫
        spanCoconeSquareIso.hom) := by
      simp only [spanSquareBoundary, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap]
    _ = stdSimplex.δ (2 : Fin 3) ≫
        (spanCoconeTriangleRight ≫ spanCoconeSquareIso.hom) := by
      rw [← joinStdSimplexIso_one_zero_inl]
      simp only [spanCoconeTriangleRight, Category.assoc, Iso.hom_inv_id_assoc]
    _ = squareLeftEdge := by
      rw [spanCoconeSquareIso_right]
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide

/-- 概要：押し出し性は余錐の coslice 射影の trivial Kan fibration 性と同値。
方針：余極限余錐の始対象の特徴づけを使う。
規約：図式は二つの始点側の辺。使われ方：押し出しの直接充填。 -/
lemma isPushoutSquare_iff_trivialKanFibration {X : SSet.{u}}
    (F : Δ[1] ⊗ Δ[1] ⟶ X) : IsPushoutSquare F ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (pushoutSpan F))
        (SSet.yonedaEquiv.symm (pushoutCocone F))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_trivialKanFibration (pushoutCocone F)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
