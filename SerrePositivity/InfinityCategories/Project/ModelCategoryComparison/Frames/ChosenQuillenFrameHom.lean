module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.QuillenReplacedFrameHom
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenMapComparison

/-!
概要：元の関手的因子分解を一般 Quillen 随伴の frame Hom 入力へ実際に代入する。
方針：cofibrant 始域とその cosimplicial 置換、元の fibrant 終域置換を同じデータから取る。
規約：独立な frame・置換保存の仮定を加えない。使われ方：一般の導来 Hom 随伴比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u vC vD
open CategoryTheory Limits HomotopicalAlgebra SSet
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
noncomputable section
variable {C : Type vC} [Category.{u} C] [ModelCategory C]
  {D : Type vD} [Category.{u} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [SerrePositivity.Quillen.IsLeftQuillen L]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations D) (fibrations D))
local notation "P" => CosimplicialFrameFamily.ofResolution (cosimplicialResolutionFamily cof)
local notation "Q" => cofibrantSource cof

/-- 元の関手的 cf 置換データだけから作る、両変数に自然な同じ frame Hom 随伴同型。 -/
def chosenQuillenFrameHomIso :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.adjunctionLeftFrameHom (L := L) (Q ⋙ (P).obj) (fibrantTarget fib) ≅
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.adjunctionRightFrameHom (R := R) (Q ⋙ (P).obj) (fibrantTarget fib) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenReplacedFrameHomIso adj P Q fib

include adj in
/-- 選択済み左像 frame の Hom は、元の fibrant 置換を標的として Kan になる。 -/
lemma chosenQuillenFrameHom_leftKan (X : Cᵒᵖ) (Y : D) :
    KanComplex
      (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.adjunctionLeftFrameHom (L := L) (Q ⋙ (P).obj) (fibrantTarget fib)).obj X).obj Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenReplacedFrame_leftHom_kanComplex adj P Q fib X Y

include adj in
/-- 同じ選択済み frame と終域置換の右像の Hom も Kan である。 -/
lemma chosenQuillenFrameHom_rightKan (X : Cᵒᵖ) (Y : D) :
    KanComplex
      (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.adjunctionRightFrameHom (R := R) (Q ⋙ (P).obj) (fibrantTarget fib)).obj X).obj Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenReplacedFrame_rightHom_kanComplex adj P Q fib X Y

/-- 左像 frame の元の augmentation は、選択した同じ cofibrant 左像への弱同値である。 -/
lemma chosenQuillenFrame_augmentation_weakEquivalence (X : C) (n : SimplexCategory) :
    weakEquivalences D
      ((Functor.whiskerRight ((P).augmentation.app ((Q).obj X)) L).app n) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenReplacedFrame_augmentation_weakEquivalence P Q (cofibrantSource_isCofibrant cof) X n

end
end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
