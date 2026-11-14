module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.QuillenLeftFrameAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.DiscreteComparison

/-!
概要：左 Quillen 像の標準導来 Hom と随伴側の元の Hom を、自然な共通 frame の Hom へ接続する。
方針：元の左像 augmentation の共通 frame の二射と、同じ随伴 Hom 同型の逆を合成する。
規約：比較は二変数の自然変換。使われ方：cf 模型への Hom 随伴比較とその局所化。
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
  (L : C ⥤ D) [SerrePositivity.Quillen.IsLeftQuillen L]
  (P : CosimplicialFrameFamily (C := C)) (Q : C ⥤ C)
  (hQ : ∀ X, IsCofibrant (Q.obj X))
  (cofD : MorphismProperty.FunctorialFactorizationData (cofibrations D) (trivialFibrations D))
  (qD : CofibrantResolutionFamily (C := D) simplex)
  (fibD : MorphismProperty.FunctorialFactorizationData (trivialCofibrations D) (fibrations D))
local notation "Img" => (Q ⋙ CosimplicialFrameFamily.obj P) ⋙
  Functor.obj (Functor.whiskeringRight SimplexCategory C D) L
local notation "aug" => _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenLeftFrameAugmentation L P Q
local notation "W" => Functor.obj (Functor.whiskeringLeft D D SSet) (fibrantTarget fibD)
local notation "M" => FrameOverFunctor.commonObj cofD qD (Q ⋙ L) Img aug

/-- 元の全族を関手上で比較した同じ共通 frame の、fibrant 終域置換を含む Hom 二変数関手。 -/
abbrev quillenDerivedHomMiddle : Cᵒᵖ ⥤ D ⥤ SSet.{u} := FrameOverFunctor.hom M ⋙ W

/-- 左像の元の標準解消 Hom から、同じ共通 Hom への二変数自然変換。 -/
def quillenDerivedHomFromLeft :
    FrameOverFunctor.hom (FrameOverFunctor.resolution qD (Q ⋙ L)) ⋙ W ⟶
      quillenDerivedHomMiddle L P Q cofD qD fibD :=
  Functor.whiskerRight (FrameOverFunctor.homLeft cofD qD (Q ⋙ L) Img aug) W

variable {R : D ⥤ C} (adj : L ⊣ R)

/-- 随伴側の元の Hom から、元の随伴同型の逆と同じ共通 frame 比較を通る自然変換。 -/
def quillenDerivedHomFromRight :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.adjunctionRightFrameHom (R := R) (Q ⋙ P.obj) (fibrantTarget fibD) ⟶
      quillenDerivedHomMiddle L P Q cofD qD fibD :=
  (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenReplacedFrameHomIso adj P Q fibD).inv ≫
    Functor.whiskerRight (FrameOverFunctor.homRight cofD qD (Q ⋙ L) Img aug) W

include hQ in
/-- 同じ共通 frame の Hom は、元の全族と fibrant 終域置換を保持した Kan 複体。 -/
lemma quillenDerivedHomMiddle_kanComplex (X : Cᵒᵖ) (Y : D) :
    KanComplex (((quillenDerivedHomMiddle L P Q cofD qD fibD).obj X).obj Y) := by
  have := fibrantTarget_isFibrant fibD Y
  exact cosimplicialHom_kanComplex ((M).obj X.unop)
    (FrameOverFunctor.commonObj_cofibrant cofD qD (Q ⋙ L) Img aug X.unop)
    (FrameOverFunctor.commonObj_homotopicallyConstant cofD qD (Q ⋙ L) Img aug
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenLeftFrameAugmentation_weak L P Q hQ) X.unop) _

include hQ in
/-- 左の元の標準導来 Hom の自然変換は、全ての元のパラメータでホモトピー同値。 -/
lemma quillenDerivedHomFromLeft_homotopyEquivalence (X : Cᵒᵖ) (Y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (((quillenDerivedHomFromLeft L P Q cofD qD fibD).app X).app Y) := by
  have := fibrantTarget_isFibrant fibD Y
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenLeftFrameCommon_left_homotopyEquivalence L P Q hQ cofD qD X
    ((fibrantTarget fibD).obj Y)

include adj hQ in
/-- 随伴側からの同じ自然変換も、全パラメータで元の Hom のホモトピー同値を与える。 -/
lemma quillenDerivedHomFromRight_homotopyEquivalence (X : Cᵒᵖ) (Y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (((quillenDerivedHomFromRight L P Q cofD qD fibD adj).app X).app Y) := by
  have := adj.isLeftAdjoint
  have := fibrantTarget_isFibrant fibD Y
  have := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenReplacedFrame_leftHom_kanComplex adj P Q fibD X Y
  have := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenReplacedFrame_rightHom_kanComplex adj P Q fibD X Y
  have : KanComplex (((FrameOverFunctor.hom M).obj X).obj ((fibrantTarget fibD).obj Y)) :=
    quillenDerivedHomMiddle_kanComplex L P Q hQ cofD qD fibD X Y
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
    ((((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenReplacedFrameHomIso adj P Q fibD).inv.app X).app Y) ≫
      ((FrameOverFunctor.homRight cofD qD (Q ⋙ L) Img aug).app X).app
        ((fibrantTarget fibD).obj Y))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso _).comp
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenLeftFrameCommon_right_homotopyEquivalence L P Q hQ cofD qD X
      ((fibrantTarget fibD).obj Y))

end
end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
