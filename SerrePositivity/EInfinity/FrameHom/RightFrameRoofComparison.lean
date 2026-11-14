module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.RightFrameFamily
public import SerrePositivity.EInfinity.FrameHom.ResolutionFixedRightComparison
public import SerrePositivity.EInfinity.FrameHom.SmallCosimplicialHomElements
public import SerrePositivity.EInfinity.FrameHom.NerveEquivalenceImage
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection

/-!
概要：元の right frame の全単体を同じ右屋根の全圏と弱比較する。
方針：反対圏の同じ解像の固定右対象比較と全単体の明示的 comma 表示を合成する。
規約：中間射を変更せず、完全な hammock への比較とは区別する。
使われ方：一般モデル圏における frame から三本矢への比較の右屋根段階。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.SimplicialModel SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 概要：元の X → V ← Y の右屋根を反対圏の同じ comma 圏で表示する。
方針：Y からの自明 cofibration を反対圏の自明 fibration として読む。
規約：対象と射の宇宙だけを揃える。使われ方：right frame の全屋根への余終性。 -/
abbrev rightFrameRoofCategory (X Y : C) :=
  CostructuredArrow (smallResolutionLeftForget.{u, v, max w u v} (C := Cᵒᵖ) (op Y))
    (AsSmall.up.obj (op X))

/-- 概要：同じ right frame の全単体から元の全右屋根への実関手。
方針：同じ射を comma に表示し、元の解像の augmentation を脚とする。
規約：反対要素圏の表示を明示する。使われ方：全三本矢との共通比較の前段。 -/
def rightFrameRoofComparison (X Y : C) :
    AsSmall.{max w u v}
      ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (r.obj.obj (op Y))).obj (op X)).Elements)ᵒᵖ) ⥤
        rightFrameRoofCategory.{u, v, w} X Y :=
  CosimplicialHomElements.smallToComma.{u, v, w} (r.obj.obj (op Y)) (op X) ⋙
    resolutionFixedRightComparison.{u, v, max w u v} (r.atObject (op Y)) (op X)

/-- 概要：同じ全単体から全右屋根への nerve の実比較は弱ホモトピー同値。
方針：明示的 comma 同値と元の固定対象比較の余終性を合成する。
規約：単体集合のモデル構造と全対象 fibrant の仮定は使わない。
使われ方：完全な hammock 比較へ進むための右屋根段階の弱同値性。 -/
lemma rightFrameRoofComparison_isWeakHomotopyEquivalence (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (rightFrameRoofComparison.{u, v, w} r X Y)) := by
  apply AnodyneWeakDetection.isWeakHomotopyEquivalence
  have hs : IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap
      (CosimplicialHomElements.smallToComma.{u, v, w} (r.obj.obj (op Y)) (op X)))) :=
    (NerveEquivalenceImage.imageIso
    (CosimplicialHomElements.smallEquivalence.{u, v, w} (r.obj.obj (op Y)) (op X))
    AnodyneHomotopy.anodyneQ (Localization.inverts _ SSet.anodyneExtensions)).isIso_hom
  have ht : IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap
      (resolutionFixedRightComparison.{u, v, max w u v} (r.atObject (op Y)) (op X)))) :=
    resolutionFixedRightComparison_localized_isIso.{u, v, max w u v}
      (r.atObject (op Y)) (op X)
  change IsIso (AnodyneHomotopy.anodyneQ.map
    (nerveMap (CosimplicialHomElements.smallToComma.{u, v, w} (r.obj.obj (op Y)) (op X)) ≫
      nerveMap (resolutionFixedRightComparison.{u, v, max w u v} (r.atObject (op Y)) (op X))))
  rw [Functor.map_comp]
  infer_instance

/-- 概要：右屋根比較の中間射は元の全単体の同じ射。
方針：二つの comma 関手の対象写像を展開する。
規約：局所化前の実射の等式。使われ方：零単体の回収と輸送。 -/
lemma rightFrameRoofComparison_middle (X Y : C)
    (s : AsSmall.{max w u v}
      ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (r.obj.obj (op Y))).obj (op X)).Elements)ᵒᵖ)) :
    (((rightFrameRoofComparison.{u, v, w} r X Y).obj s).hom).down.unop =
      (AsSmall.down.obj s).unop.val.unop := rfl

end SerrePositivity.EInfinity.FrameHom
