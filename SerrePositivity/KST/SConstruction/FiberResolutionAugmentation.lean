module
public import SerrePositivity.KST.SConstruction.FiberResolutionContraction
public import SerrePositivity.KST.SConstruction.DiscreteNerveConstant

/-! # 左 fiber の二重単体解消の augmentation の弱同値
概要：固定係数次数の縮約を自然な二重単体比較に束ね、対角から X への弱同値を得る。
方針：元の単体への射影を行ごとに離散値へ送り、行の局所化同型を対角へ移す。
規約：Quillen A や加法性を仮定しない。使われ方：単体積版 Quillen A の X 側の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.SimplicialModel SerrePositivity.BisimplicialModel
open scoped Simplicial

/-- 概要：固定係数次数の因子分解の nerve から元の単体の定値単体集合への射。
方針：射列の最初の対象の元の X 単体を取る。
規約：反対圏の射も元の単体を保持する。使われ方：二重単体 augmentation の各行。 -/
def fiberResolutionRowAugmentation {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    nerve (fiberResolutionCategory f n)ᵒᵖ ⟶
      (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj (X _⦋n⦌) where
  app m := ↾fun c => fiberResolutionValue f (c.obj 0).unop
  naturality {m l} σ := by
    apply ConcreteCategory.hom_ext
    intro c
    exact fiberResolutionValue_map f (c.map (homOfLE (Fin.zero_le (σ.unop.toOrderHom 0)))).unop

/-- 概要：行の augmentation は離散圏への関手の nerve と離散 nerve の同型の合成。
方針：射列の最初の対象で計算する。
規約：元の射全体の等号。使われ方：行の局所化同型の検証。 -/
lemma fiberResolutionRowAugmentation_eq {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    fiberResolutionRowAugmentation f n =
      resolutionNerveMap (fiberResolutionValueFunctor f n) ≫
        (discreteNerveConstantIso (X _⦋n⦌)).hom := rfl

/-- 概要：固定係数次数の augmentation は anodyne 局所化で同型。
方針：標準因子分解による縮約と離散 nerve の厳密な同型。
規約：モデル構造や Kan 性を要求しない。使われ方：対角の比較の入力。 -/
lemma fiberResolutionRowAugmentation_localized_isIso {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (fiberResolutionRowAugmentation f n)) := by
  have := fiberResolutionValueFunctor_localized_isIso f n
  rw [fiberResolutionRowAugmentation_eq, AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

/-- 概要：行の augmentation は係数次数に関しても自然な二重単体比較。
方針：各左 fiber の第一射影の単体的自然性を使う。
規約：内外両方の単体作用素で自然。使われ方：解消から X への対角の射。 -/
def fiberResolutionRowsAugmentation {X Y : SSet.{u}} (f : X ⟶ Y) :
    elementsResolution (simplexFiberDiagram f) ⟶
      X ⋙ CategoryTheory.Functor.const SimplexCategoryᵒᵖ where
  app n := fiberResolutionRowAugmentation f n.unop.len
  naturality {n l} σ := by
    rcases n with ⟨⟨n⟩⟩
    rcases l with ⟨⟨l⟩⟩
    apply SSet.hom_ext
    intro m
    apply ConcreteCategory.hom_ext
    intro c
    let e := (c.obj 0).unop
    change (simplexLeftFiberProjection f e.obj.unop.val).app (Opposite.op ⦋l⦌)
      ((simplexLeftFiber f e.obj.unop.val).map σ e.val) =
        X.map σ ((simplexLeftFiberProjection f e.obj.unop.val).app (Opposite.op ⦋n⦌) e.val)
    exact ConcreteCategory.congr_hom
      ((simplexLeftFiberProjection f e.obj.unop.val).naturality σ) e.val

/-- 概要：各次数を定値にした図式の対角は元の単体集合。
方針：各次数の元をそのまま使う。
規約：元の単体作用素を保つ厳密な同型。使われ方：augmentation の値域の同定。 -/
def constantRowsDiagonalIso (X : SSet.{u}) :
    diagonal.obj (X ⋙ CategoryTheory.Functor.const SimplexCategoryᵒᵖ) ≅ X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- 概要：左 fiber の二重単体解消の対角から元の X への実際の augmentation。
方針：自然な行の augmentation の対角に値域の厳密な同型を合成する。
規約：他の比較に置換しない。使われ方：単体積版 Quillen A の二方向の比較。 -/
def fiberResolutionAugmentation {X Y : SSet.{u}} (f : X ⟶ Y) :
    diagonal.obj (elementsResolution (simplexFiberDiagram f)) ⟶ X :=
  diagonal.map (fiberResolutionRowsAugmentation f) ≫ (constantRowsDiagonalIso X).hom

/-- 概要：任意の射の左 fiber 解消の対角から X への augmentation は局所化同型。
方針：全係数次数の縮約を行ごとの局所化同型として対角へ移す。
規約：f の fiber の可縮性を仮定しない。使われ方：単体積版 Quillen A の解消の比較。 -/
lemma fiberResolutionAugmentation_localized_isIso {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsIso (AnodyneHomotopy.anodyneQ.map (fiberResolutionAugmentation f)) := by
  have := localized_diagonal_map (fiberResolutionRowsAugmentation f)
    (fun n => fiberResolutionRowAugmentation_localized_isIso f n.unop.len)
  rw [fiberResolutionAugmentation, AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

end SerrePositivity.KST.SConstruction
