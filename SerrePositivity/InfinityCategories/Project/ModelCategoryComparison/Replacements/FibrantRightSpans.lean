module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.RightFrameReplacement
public import SerrePositivity.EInfinity.FrameHom.FullyFaithfulNerveRetraction
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection

/-!
概要：一般モデル圏の特殊三本矢を fibrant な右終域の全図式へ制限できる。
方針：同じ right frame の次数零で右終域を関手的に置き換え、元の単位を自然変換にする。
規約：両端点と左脚を保ち、全対象 fibrant の仮定を置かない。
使われ方：代数専用の frame 比較を任意モデル圏へ一般化する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FibrantRightSpans
open CategoryTheory HomotopicalAlgebra Opposite
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.SimplicialModel
open _root_.SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex) (X Y : C)

/-- 概要：右終域が fibrant な元の特殊三本矢の性質。
方針：元の右対象の fibrancy を指定する。
規約：全部分圏として使う。使われ方：全右脚の Hom 不変性。 -/
def property : ObjectProperty (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y) := fun S => IsFibrant S.right

/-- 概要：fibrant な右終域を持つ三本矢の全部分圏。
方針：同じ三本矢の全射を残す。
規約：両端点は元のまま。使われ方：全図式の fibrant 制限。 -/
abbrev FibrantSpan := (property X Y).FullSubcategory

/-- 概要：同じ全図式への元の包含。
方針：全部分圏の包含を使う。
規約：三射を変更しない。使われ方：弱比較の実射。 -/
abbrev inclusion : FibrantSpan X Y ⥤ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y := (property X Y).ι

/-- 概要：右終域だけを同じ right frame の次数零へ送る。
方針：右脚と中間射に同じ augmentation を後合成する。
規約：両端点と左脚を保持。使われ方：fibrant 制限への関手的な戻し。 -/
def replacedObject (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y) : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y where
  left := S.left
  right := (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r).obj S.right
  leftMap := S.leftMap
  middle := S.middle ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app S.right
  rightMap := S.rightMap ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app S.right
  left_mem := S.left_mem
  right_mem := (trivialCofibrations C).comp_mem _ _ S.right_mem
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit_trivialCofibration r S.right)

/-- 概要：全三本矢の右終域の実置換関手。
方針：右縦射を同じ置換関手で送り、単位の自然性を使う。
規約：元の全射に定義する。使われ方：fibrant な全図式との比較。 -/
def replacement : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y ⥤ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y where
  obj := replacedObject r X Y
  map {S T} f := {
    left := f.left
    right := (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r).map f.right
    left_w := f.left_w
    middle_w := by
      change (S.middle ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app S.right) ≫ _ =
        f.left ≫ (T.middle ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app T.right)
      rw [CategoryTheory.Category.assoc, ← (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).naturality,
        Functor.id_map, ← CategoryTheory.Category.assoc, f.middle_w,
        CategoryTheory.Category.assoc]
    right_w := by
      change (S.rightMap ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app S.right) ≫ _ =
        T.rightMap ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app T.right
      rw [CategoryTheory.Category.assoc, ← (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).naturality,
        Functor.id_map, ← CategoryTheory.Category.assoc, f.right_w] }
  map_id S := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext _ _ rfl ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r).map_id S.right)
  map_comp f g := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext _ _ rfl ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r).map_comp f.right g.right)

/-- 概要：同じ実置換を fibrant な全部分圏へ束ねる。
方針：right frame の各値の fibrancy を使う。
規約：同じ関手の lift。使われ方：包含の自然な逆の候補。 -/
def retraction : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y ⥤ FibrantSpan X Y :=
  (property X Y).lift (replacement r X Y)
    (fun S => by
      dsimp [property, replacement, replacedObject]
      exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement_isFibrant r S.right)

/-- 概要：元の三本矢から同じ右終域の置換への実縦射。
方針：左は恒等射、右は同じ augmentation を使う。
規約：元の両端点を保持。使われ方：全図式の自然な単位の成分。 -/
def unitMap (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y) : S ⟶ replacedObject r X Y S := by
  dsimp only [replacedObject]
  exact {
    left := 𝟙 S.left
    right := (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app S.right
    left_w := CategoryTheory.Category.id_comp _
    middle_w := (CategoryTheory.Category.id_comp _).symm
    right_w := rfl }

/-- 概要：元の全図式から同じ右終域の置換への自然な単位。
方針：左縦射を恒等射、右縦射を元の augmentation とする。
規約：三本矢の全射で自然。使われ方：元の包含の nerve の反転。 -/
def unit : 𝟭 (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y) ⟶ retraction r X Y ⋙ inclusion X Y where
  app S := by
    change S ⟶ replacedObject r X Y S
    exact unitMap r X Y S
  naturality S T f := by
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext
    · change f.left ≫ 𝟙 T.left = 𝟙 S.left ≫ f.left
      simp only [CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id]
    · change f.right ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app T.right =
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app S.right ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r).map f.right
      exact (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).naturality f.right

include r in
/-- 概要：fibrant な右終域の全図式の元の包含は anodyne 局所化で可逆。
方針：充満忠実な包含と同じ実単位による nerve の収縮を使う。
規約：全対象の fibrancy を仮定しない。使われ方：一般モデルの frame 比較。 -/
lemma inclusion_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (inclusion X Y))) :=
  _root_.SerrePositivity.EInfinity.FrameHom.FullyFaithfulNerveRetraction.of_unit (inclusion X Y) (retraction r X Y) (unit r X Y)

include r in
/-- 概要：同じ fibrant 制限の包含の nerve 自身は弱ホモトピー同値。
方針：同じ anodyne 反転後の同型性を全 Kan 標的で検出する。
規約：単体集合モデルを使わない。使われ方：元の三本矢との弱比較。 -/
lemma inclusion_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (inclusion X Y)) :=
  _root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (inclusion_localized_isIso r X Y)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FibrantRightSpans
