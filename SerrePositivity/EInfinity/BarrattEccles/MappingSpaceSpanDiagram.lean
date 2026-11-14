module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceSpans
public import SerrePositivity.EInfinity.FrameHom.ArrowSpanGrothendieck
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.TargetInvariance
public import SerrePositivity.EInfinity.FrameHom.NerveEquivalenceImage
public import SerrePositivity.EInfinity.BarrattEccles.Fibrancy

/-!
# 実際の Map^h の比較と右脚の全図式

概要：任意の可換環上の元の三本矢の全図式と同じ Map^h の比較を表示する。
方針：同じ転送モデル・分解・全対象の fibrancy を局所的に代入する。
規約：元の代数の cofibrancy や単体集合モデルを要求しない。
使われ方：分解の余終性と右脚の Hom 図式の不変性による右比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.Reedy
open SerrePositivity.SimplicialModel

variable (A : Type u) [CommRing A]

/-- 概要：元の E 代数からの全自明 cofibration の slice（Low 命題 3.7）。
方針：実際の転送モデルの右脚の類を使う。
規約：全ての元の対象と可換三角形を保持する。
使われ方：三本矢の右変数の全図式の底。 -/
abbrev algebraRightSpanBase (Y : (operad A).Algebra) :=
  let := modelCategory A
  (trivialCofibrations (operad A).Algebra).Under ⊤ Y

/-- 概要：元の E 代数の三本矢の右変数の全 Cat 値図式（Low 命題 3.7）。
方針：同じモデル構造と両脚の射の類を一般の表示へ代入する。
規約：元の中間射と全ての両脚を含める。
使われ方：実際の三本矢の圏の Grothendieck 表示。 -/
abbrev algebraSpanRightDiagram (X Y : (operad A).Algebra) :
    algebraRightSpanBase A Y ⥤ Cat.{u, u + 1} :=
  let := modelCategory A
  FrameHom.ArrowSpan.rightDiagram (trivialFibrations (operad A).Algebra)
    (trivialCofibrations (operad A).Algebra) X Y

/-- 概要：右変数の全図式から元の三本矢への回収（Low 命題 3.7）。
方針：同じモデルの元の両脚と中間射を取り出す。
規約：元の三本矢の圏を比較先に使う。
使われ方：元の Map^h の比較射の厳密な回収。 -/
def algebraSpanFromGrothendieck (X Y : (operad A).Algebra) :
    Grothendieck (algebraSpanRightDiagram A X Y) ⥤ algebraSpecialHammock A X Y := by
  let := modelCategory A
  exact FrameHom.ArrowSpan.fromGrothendieck _ _ X Y

/-- 概要：元の三本矢の全図式の実際の圏同値（Low 命題 3.7）。
方針：同じ両脚の slice の明示的な順逆の一般の表示を代入する。
規約：元の三本矢の対象・全射を保持する。
使われ方：三本矢の全図式への余終性の適用。 -/
def algebraSpanGrothendieckEquivalence (X Y : (operad A).Algebra) :
    Grothendieck (algebraSpanRightDiagram A X Y) ≌ algebraSpecialHammock A X Y := by
  let := modelCategory A
  exact FrameHom.ArrowSpan.grothendieckEquivalence _ _ X Y

/-- 概要：同じ Map^h の全単体の比較を右脚の全図式へ送る（Low 命題 3.7）。
方針：元の比較関手の後に同じ元の三射の表示関手を置く。
規約：元の Map^h・分解・fibrant 置換を変更しない。
使われ方：右射の反転性を元の射で証明するための因子分解。 -/
def mappingSpaceSpanGrothendieckFunctor (X Y : (operad A).Algebra) :
    ((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ ⥤
      Grothendieck (algebraSpanRightDiagram A X Y) := by
  let := modelCategory A
  exact mappingSpaceSpecialHammockFunctor A X Y ⋙
    FrameHom.ArrowSpan.toGrothendieck _ _ X Y

/-- 概要：全図式を回収すると元の Map^h の同じ比較関手（Low 命題 3.7）。
方針：同じ元の三射の表示の厳密な逆則を使う。
規約：全単体と全作用素の厳密な関手の等式。
使われ方：特殊な三本矢への元の右射との一致。 -/
lemma mappingSpaceSpanGrothendieckFunctor_fac (X Y : (operad A).Algebra) :
    mappingSpaceSpanGrothendieckFunctor A X Y ⋙ algebraSpanFromGrothendieck A X Y =
      mappingSpaceSpecialHammockFunctor A X Y := by
  let := modelCategory A
  change (mappingSpaceSpecialHammockFunctor A X Y ⋙
    FrameHom.ArrowSpan.toGrothendieck _ _ X Y) ⋙
      FrameHom.ArrowSpan.fromGrothendieck _ _ X Y = _
  rw [CategoryTheory.Functor.assoc, FrameHom.ArrowSpan.toGrothendieck_fromGrothendieck,
    CategoryTheory.Functor.comp_id]

/-- 概要：右脚の全図式上の元の分解の Hom（Low 命題 3.7）。
方針：同じ分解の cosimplicial Hom に元の右脚の終域を代入する。
規約：元の分解と全ての後合成を保持する。
使われ方：全右脚の図式のホモトピー不変性の検査。 -/
def mappingRightHomDiagram (X Y : (operad A).Algebra) :
    algebraRightSpanBase A Y ⥤ SSet.{u} := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.rightSliceForget (trivialCofibrations (operad A).Algebra) Y ⋙
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((cosimplicialResolutionFamily (mappingCofibrantFactorization A)).obj.obj X)

/-- 概要：全右脚の全遷移で同じ Hom の像は反転可能（Low 命題 3.7）。
方針：元の両右脚の擬同型性と全代数の fibrancy から終域不変性を適用する。
規約：任意の可換環・全右脚を扱い、単体集合モデルを入力しない。
使われ方：固定した右端の Hom と右変数の全図式の比較。 -/
lemma mappingRightHomDiagram_map_localized_isIso {X Y : (operad A).Algebra}
    {s t : algebraRightSpanBase A Y} (f : s ⟶ t) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((mappingRightHomDiagram A X Y).map f)) := by
  let := modelCategory A
  have hw : weakEquivalences (operad A).Algebra f.right := by
    apply (weakEquivalences (operad A).Algebra).of_precomp s.hom _ s.prop.2
    exact (Under.w f.hom).symm ▸ t.prop.2
  have : WeakEquivalence f.right := ⟨hw⟩
  have : IsFibrant s.right := isFibrant A s.right
  have : IsFibrant t.right := isFibrant A t.right
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.target_weakEquivalence_isIso _
    ((cosimplicialResolutionFamily (mappingCofibrantFactorization A)).cofibrant X)
    AnodyneHomotopy.anodyneQ (Localization.inverts _ SSet.anodyneExtensions) f.right

/-- 概要：元の全単体の始域から右脚の全図式の nerve への射（Low 命題 3.7）。
方針：同じ射列の Hom の宇宙だけを down し、元の表示関手を適用する。
規約：元の右射と同じ始域の nerve を使う。
使われ方：元の右比較の反転性の中間射。 -/
def mappingSpaceSpanGrothendieckNerveMap (X Y : (operad A).Algebra) :
    nerve (ULiftHom.{u + 1} (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      nerve (Grothendieck (algebraSpanRightDiagram A X Y)) where
  app _ := ↾fun c => c ⋙ ULiftHom.down.{0, u, u + 1} ⋙
    mappingSpaceSpanGrothendieckFunctor A X Y
  naturality _ _ _ := rfl

/-- 概要：右脚の全図式の nerve から元の三本矢の nerve への射（Low 命題 3.7）。
方針：元の明示的な回収関手の nerve を使う。
規約：元の三本矢の圏を比較先に使う。
使われ方：元の右比較の厳密な回収。 -/
def algebraSpanFromGrothendieckNerveMap (X Y : (operad A).Algebra) :
    nerve (Grothendieck (algebraSpanRightDiagram A X Y)) ⟶
      nerve (algebraSpecialHammock A X Y) :=
  nerveMap (algebraSpanFromGrothendieck A X Y)

/-- 概要：同じ全図式の nerve を経由すると元の右射そのもの（Low 命題 3.7）。
方針：元の関手の厳密な回収を全射列へ適用する。
規約：全単体・全作用素で元の比較射に等しい。
使われ方：右射の反転性の同じ中間図式への帰着。 -/
lemma mappingSpaceSpanGrothendieckNerveMap_fac (X Y : (operad A).Algebra) :
    mappingSpaceSpanGrothendieckNerveMap A X Y ≫
        algebraSpanFromGrothendieckNerveMap A X Y = mappingSpaceSpecialHammockNerveMap A X Y := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  change (c ⋙ ULiftHom.down.{0, u, u + 1} ⋙ mappingSpaceSpanGrothendieckFunctor A X Y) ⋙
      algebraSpanFromGrothendieck A X Y =
    c ⋙ ULiftHom.down.{0, u, u + 1} ⋙ mappingSpaceSpecialHammockFunctor A X Y
  rw [CategoryTheory.Functor.assoc, CategoryTheory.Functor.assoc,
    mappingSpaceSpanGrothendieckFunctor_fac]

/-- 概要：全図式から元の三本矢への nerve の回収は反転可能（Low 命題 3.7）。
方針：元の明示的な圏同値の単位・余単位のホモトピーを使う。
規約：順射は同じ元の回収関手の nerve で、単体集合モデルを要求しない。
使われ方：元の右射の反転性を全図式への中間射へ帰着する。 -/
lemma algebraSpanFromGrothendieckNerveMap_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map (algebraSpanFromGrothendieckNerveMap A X Y)) :=
  inferInstanceAs (IsIso (FrameHom.NerveEquivalenceImage.imageIso
    (algebraSpanGrothendieckEquivalence A X Y) AnodyneHomotopy.anodyneQ
    (Localization.inverts _ SSet.anodyneExtensions)).hom)

/-- 概要：元の右射の反転性は同じ全図式への中間射の反転性と同値（Low 命題 3.7）。
方針：元の右射の厳密な因子分解と回収射の反転性を使う。
規約：元の比較射を変更せず、反転性の未証明部分を明示する。
使われ方：全右脚の図式へのホモトピー余終性の適用先。 -/
lemma mappingSpaceSpecialHammockNerveMap_localized_isIso_iff (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map (mappingSpaceSpecialHammockNerveMap A X Y)) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map (mappingSpaceSpanGrothendieckNerveMap A X Y)) := by
  rw [← mappingSpaceSpanGrothendieckNerveMap_fac, CategoryTheory.Functor.map_comp]
  have := algebraSpanFromGrothendieckNerveMap_localized_isIso A X Y
  exact isIso_comp_right_iff _ _

end SerrePositivity.EInfinity.BarrattEccles
