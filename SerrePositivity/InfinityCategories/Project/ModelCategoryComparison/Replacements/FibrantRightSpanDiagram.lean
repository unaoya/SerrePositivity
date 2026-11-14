module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.FibrantRightSpans
public import SerrePositivity.EInfinity.FrameHom.ArrowSpanGrothendieck

/-!
概要：fibrant な右終域の三本矢を元の全右脚の Cat 値図式として表示する。
方針：右脚の全部分圏と左脚の comma を元の射で往復する。
規約：三本矢の両端点と三射を保ち、全対象 fibrant は仮定しない。
使われ方：任意モデル圏で標的不変性と分解の余終性を全図式へ適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory Limits HomotopicalAlgebra
variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)

/-- 概要：元の右脚の終域が fibrant である性質。
方針：右脚の同じ終域を読む。
規約：全部分圏として使う。使われ方：Hom の標的不変性。 -/
def baseProperty : ObjectProperty ((trivialCofibrations C).Under ⊤ Y) :=
  fun s => IsFibrant s.right

/-- 概要：fibrant な右終域を持つ元の全右脚の圏。
方針：元の全自明 cofibration の coslice の全部分圏を取る。
規約：元の全可換三角形。使われ方：三本矢の全図式の底。 -/
abbrev Base := (baseProperty Y).FullSubcategory

/-- 概要：元の全右脚から同じ fibrant 終域への射影。
方針：元の全部分圏の包含と右脚の射影を合成する。
規約：元の対象と射。使われ方：全中間 Hom の共変変数。 -/
abbrev forget : Base Y ⥤ C := (baseProperty Y).ι ⋙
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.rightSliceForget (trivialCofibrations C) Y

/-- 概要：同じ全左脚と fibrant な全右脚による Cat 値図式。
方針：元の左脚射影と右脚射影の comma を束ねる。
規約：元の全中間射。使われ方：三本矢の全図式の Grothendieck 表示。 -/
abbrev diagram : Base Y ⥤ Cat.{v, max u v} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.diagram (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.leftSliceForget (trivialFibrations C) X) (forget Y)

/-- 概要：元の fibrant な三本矢を同じ両脚の comma に送る。
方針：元の三射と右終域の fibrancy をそのまま使う。
規約：対象と全射を変更しない。使われ方：全図式の明示的な表示。 -/
def toComma : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FibrantRightSpans.FibrantSpan X Y ⥤
    Comma (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.leftSliceForget (trivialFibrations C) X) (forget Y) where
  obj S := {
    left := MorphismProperty.Over.mk ⊤ S.obj.leftMap S.obj.left_mem
    right := ⟨MorphismProperty.Under.mk ⊤ S.obj.rightMap S.obj.right_mem, S.property⟩
    hom := S.obj.middle }
  map f := {
    left := MorphismProperty.Over.homMk f.hom.left f.hom.left_w
    right := ObjectProperty.homMk (MorphismProperty.Under.homMk f.hom.right f.hom.right_w)
    w := f.hom.middle_w.symm }
  map_id _ := CommaMorphism.ext rfl rfl
  map_comp _ _ := CommaMorphism.ext rfl rfl

/-- 概要：同じ両脚の comma から元の fibrant 三本矢を回収する。
方針：同じ元の対象と三射と fibrancy を束ねる。
規約：同型類の代表を選ばない。使われ方：全図式の逆の表示。 -/
def fromComma :
    Comma (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.leftSliceForget (trivialFibrations C) X) (forget Y) ⥤
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FibrantRightSpans.FibrantSpan X Y where
  obj S := ⟨{
    left := S.left.left
    right := S.right.obj.right
    leftMap := S.left.hom
    middle := S.hom
    rightMap := S.right.obj.hom
    left_mem := S.left.prop
    right_mem := S.right.obj.prop }, S.right.property⟩
  map f := ObjectProperty.homMk {
    left := f.left.left
    right := f.right.hom.right
    left_w := Over.w f.left.hom
    middle_w := f.w.symm
    right_w := Under.w f.right.hom.hom }
  map_id _ := by
    apply ObjectProperty.hom_ext
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext _ _ rfl rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext _ _ rfl rfl

/-- 概要：元の comma の回収は同じ左縦射を保つ。
方針：同じ実関手の定義を読む。規約：全射。使われ方：全単体の照合。 -/
lemma fromComma_map_left
    {S T : Comma (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.leftSliceForget (trivialFibrations C) X) (forget Y)} (f : S ⟶ T) :
    ((fromComma X Y).map f).hom.left = f.left.left := rfl

/-- 概要：元の comma の回収は同じ右縦射を保つ。
方針：同じ実関手の定義を読む。規約：全射。使われ方：全単体の照合。 -/
lemma fromComma_map_right
    {S T : Comma (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.leftSliceForget (trivialFibrations C) X) (forget Y)} (f : S ⟶ T) :
    ((fromComma X Y).map f).hom.right = f.right.hom.right := rfl

/-- 概要：元の fibrant 三本矢の両脚表示は明示的な圏同値。
方針：同じ元の三射の順逆を恒等の成分で比較する。
規約：順射は元の全対象・全射を保つ。使われ方：三本矢の全図式への回収。 -/
def commaEquivalence : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FibrantRightSpans.FibrantSpan X Y ≌
    Comma (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.leftSliceForget (trivialFibrations C) X) (forget Y) :=
  CategoryTheory.Equivalence.mk (toComma X Y) (fromComma X Y)
    (NatIso.ofComponents (fun S => Iso.refl S))
    (NatIso.ofComponents (fun S =>
      Comma.isoMk (MorphismProperty.Over.isoMk (Iso.refl S.left.left)
        (Category.id_comp S.left.hom))
        ((baseProperty Y).isoMk (MorphismProperty.Under.isoMk (Iso.refl S.right.obj.right)
          (Category.comp_id S.right.obj.hom)))
        ((Category.id_comp S.hom).trans (Category.comp_id S.hom).symm)) (by
      intro S T f
      apply CommaMorphism.ext
      · apply MorphismProperty.Over.Hom.ext
        change f.left.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left.left
        simp
      · apply ObjectProperty.hom_ext
        apply MorphismProperty.Under.Hom.ext
        change f.right.hom.right ≫ 𝟙 _ = 𝟙 _ ≫ f.right.hom.right
        simp))

/-- 概要：同じ全右脚上の全図式は元の fibrant 三本矢の圏と同値。
方針：元の comma の Grothendieck 表示と両脚の明示的な同値を合成する。
規約：全元の射を保持。使われ方：全図式の余終性から元の三本矢への輸送。 -/
def grothendieckEquivalence : Grothendieck (diagram X Y) ≌
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FibrantRightSpans.FibrantSpan X Y :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.equivalence _ _).trans (commaEquivalence X Y).symm

variable [IsFibrant Y]

/-- 概要：元の fibrant な Y の恒等右脚は同じ底の対象。
方針：元の恒等射と同じ fibrancy を使う。
規約：元の Y 自身。使われ方：全図式の始対象。 -/
def initial : Base Y := ⟨_root_.SerrePositivity.EInfinity.FrameHom.ArrowSpan.rightSliceInitial (trivialCofibrations C) Y,
  show IsFibrant Y from inferInstance⟩

/-- 概要：元の恒等右脚は fibrant な全右脚の圏の始対象。
方針：元の全右脚の唯一の可換三角形を全部分圏へ持ち上げる。
規約：元の全射。使われ方：固定した右脚の fiber の包含の弱比較。 -/
def initial_isInitial : IsInitial (initial Y) :=
  IsInitial.ofUniqueHom
    (fun t => ObjectProperty.homMk
      ((_root_.SerrePositivity.EInfinity.FrameHom.ArrowSpan.rightSliceInitial_isInitial (trivialCofibrations C) Y).to t.obj)) (by
      intro t f
      apply ObjectProperty.hom_ext
      exact (_root_.SerrePositivity.EInfinity.FrameHom.ArrowSpan.rightSliceInitial_isInitial (trivialCofibrations C) Y).hom_ext _ _)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
