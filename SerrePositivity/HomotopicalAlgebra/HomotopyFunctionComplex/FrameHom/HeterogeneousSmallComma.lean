module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.GrothendieckConstruction.CommaGrothendieck
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveAsSmall
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage

/-!
概要：異なる対象・Hom 宇宙を持つ二関手の comma を同じ小圏へ揃える。
方針：元の対象と射を up/down する明示的な順逆を使う。
規約：既存の SmallCommaGrothendieck は変更せず、宇宙一般化を別の葉とする。
使われ方：任意モデル圏の全左脚と fibrant な全右脚の図式の実回収。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uK vK uJ vJ uC vC w
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma
open _root_.CategoryTheory
open _root_.SerrePositivity.SimplicialModel
variable {K : Type uK} [Category.{vK} K] {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] (Q : K ⥤ C) (R : J ⥤ C)

/-- 概要：異なる宇宙の関手の前後を同じ指定宇宙へ持ち上げる。
方針：元の up/down を使う。
規約：対象と全射を保つ。使われ方：同じ宇宙の comma の両関手。 -/
abbrev liftFunctor (F : K ⥤ C) : AsSmall.{w} K ⥤ AsSmall.{w} C :=
  AsSmall.down.{vK, uK, w} ⋙ F ⋙ AsSmall.up.{vC, uC, w}

/-- 概要：両関手の全宇宙を揃えた同じ小さい comma。
方針：全対象と全射の包みを共通の宇宙へ送る。
規約：中間射は元の同じ射。使われ方：全図式の宇宙の一致。 -/
abbrev SmallComma := Comma
  (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.liftFunctor.{uK, vK, uC, vC, max w uK vK uJ vJ uC vC} Q)
  (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.liftFunctor.{uJ, vJ, uC, vC, max w uK vK uJ vJ uC vC} R)

/-- 概要：同じ小さい comma の元のデータを down する。
方針：二つの対象と中間射と二つの縦射を元の包みから取り出す。
規約：全射を保つ。使われ方：元の comma の宇宙表示への回収。 -/
def down : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.SmallComma.{uK, vK, uJ, vJ, uC, vC, w} Q R ⥤
    AsSmall.{max w uK vK uJ vJ uC vC} (Comma Q R) where
  obj S := AsSmall.up.obj ⟨
    AsSmall.down.{vK, uK, max w uK vK uJ vJ uC vC}.obj S.left,
    AsSmall.down.{vJ, uJ, max w uK vK uJ vJ uC vC}.obj S.right,
    AsSmall.down.{vC, uC, max w uK vK uJ vJ uC vC}.map S.hom⟩
  map f := AsSmall.up.map ⟨
    AsSmall.down.{vK, uK, max w uK vK uJ vJ uC vC}.map f.left,
    AsSmall.down.{vJ, uJ, max w uK vK uJ vJ uC vC}.map f.right,
    congrArg ULift.down f.w⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 概要：元の comma の同じデータを共通宇宙へ up する。
方針：元の二対象と中間射をそのまま持ち上げる。
規約：元の全射を保つ。使われ方：同じ小さい comma への逆。 -/
def up : AsSmall.{max w uK vK uJ vJ uC vC} (Comma Q R) ⥤
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.SmallComma.{uK, vK, uJ, vJ, uC, vC, w} Q R where
  obj S := ⟨AsSmall.up.{vK, uK, max w uK vK uJ vJ uC vC}.obj (AsSmall.down.obj S).left,
    AsSmall.up.{vJ, uJ, max w uK vK uJ vJ uC vC}.obj (AsSmall.down.obj S).right,
    AsSmall.up.{vC, uC, max w uK vK uJ vJ uC vC}.map (AsSmall.down.obj S).hom⟩
  map f := ⟨AsSmall.up.{vK, uK, max w uK vK uJ vJ uC vC}.map (AsSmall.down.map f).left,
    AsSmall.up.{vJ, uJ, max w uK vK uJ vJ uC vC}.map (AsSmall.down.map f).right, by
      apply ULift.ext
      exact (AsSmall.down.map f).w⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 概要：元の小さい comma の全データは順逆で厳密に戻る。
方針：元の up/down の定義を評価する。
規約：全対象と全射の等式。使われ方：明示的な宇宙比較の単位。 -/
lemma down_up :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.down.{uK, vK, uJ, vJ, uC, vC, w} Q R ⋙
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.up.{uK, vK, uJ, vJ, uC, vC, w} Q R = 𝟭 _ := rfl

/-- 概要：元の comma の小圏も同じ順逆で厳密に戻る。
方針：包みの eta 則を評価する。
規約：元のデータを保つ。使われ方：明示的な宇宙比較の余単位。 -/
lemma up_down :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.up.{uK, vK, uJ, vJ, uC, vC, w} Q R ⋙
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.down.{uK, vK, uJ, vJ, uC, vC, w} Q R = 𝟭 _ := rfl

/-- 概要：異なる宇宙の同じ comma の明示的な小圏同値。
方針：元の二つの厳密な順逆を使う。
規約：順関手は元の down。使われ方：全図式の元の三本矢への回収。 -/
def equivalence : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.SmallComma.{uK, vK, uJ, vJ, uC, vC, w} Q R ≌
    AsSmall.{max w uK vK uJ vJ uC vC} (Comma Q R) :=
  CategoryTheory.Equivalence.mk (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.down.{uK, vK, uJ, vJ, uC, vC, w} Q R)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.up.{uK, vK, uJ, vJ, uC, vC, w} Q R)
    (eqToIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.down_up.{uK, vK, uJ, vJ, uC, vC, w} Q R).symm)
    (eqToIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.up_down.{uK, vK, uJ, vJ, uC, vC, w} Q R))

/-- 概要：同じ小さい全図式から元の comma の小圏へ回収する明示的な同値。
方針：元の Grothendieck 表示と同じ up/down の順逆を合成する。
規約：元の全射を保つ。使われ方：一般モデルの全図式の回収。 -/
def grothendieckEquivalence : Grothendieck (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.diagram
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.liftFunctor.{uK, vK, uC, vC, max w uK vK uJ vJ uC vC} Q)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.liftFunctor.{uJ, vJ, uC, vC, max w uK vK uJ vJ uC vC} R)) ≌
      AsSmall.{max w uK vK uJ vJ uC vC} (Comma Q R) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.equivalence _ _).trans
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.equivalence.{uK, vK, uJ, vJ, uC, vC, w} Q R)

/-- 概要：元の小さい全図式から同じ元の comma の nerve への実回収。
方針：同じ元の全射を down し、同じ nerve の宇宙表示へ移す。
規約：全単体と全作用素を保持。使われ方：元の三本矢の実射との照合。 -/
def recoveryNerveMap : nerve (Grothendieck (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.diagram
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.liftFunctor.{uK, vK, uC, vC, max w uK vK uJ vJ uC vC} Q)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.liftFunctor.{uJ, vJ, uC, vC, max w uK vK uJ vJ uC vC} R))) ⟶
      SSet.uliftFunctor.{max w uK vK uJ vJ uC vC, max uK uJ vC vK vJ}.obj
        (nerve (Comma Q R)) :=
  nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.grothendieckEquivalence.{uK, vK, uJ, vJ, uC, vC, w} Q R).functor ≫
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveAsSmall.iso.{max uK uJ vC, max vK vJ, max w uK vK uJ vJ uC vC} (Comma Q R)).hom

/-- 概要：同じ実回収射は anodyne 反転後に可逆。
方針：明示的な圏同値の同じ順射と nerve の実同型を使う。
規約：単体集合モデルは使わない。使われ方：全図式から元の三本矢への弱比較。 -/
lemma recoveryNerveMap_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.recoveryNerveMap.{uK, vK, uJ, vJ, uC, vC, w} Q R)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.grothendieckEquivalence.{uK, vK, uJ, vJ, uC, vC, w} Q R).functor)) :=
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage.imageIso
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.grothendieckEquivalence.{uK, vK, uJ, vJ, uC, vC, w} Q R)
      AnodyneHomotopy.anodyneQ (Localization.inverts _ SSet.anodyneExtensions)).isIso_hom
  dsimp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.recoveryNerveMap]
  rw [Functor.map_comp]
  infer_instance

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma
