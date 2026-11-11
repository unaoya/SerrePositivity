module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.QuillenDerivedHomComparison
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ResolutionHomSourceRestriction
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ResolutionHomTargetReplacement

/-!
概要：元の三つの因子分解だけで標準導来 Hom の左右を同じ Kan な自然比較へ接続する。
方針：左側は LQ の標準解消、右側は X の標準解消と RRY を使い、元の始域比較で二重置換を戻す。
規約：元の自然変換と全パラメータを保持。使われ方：導来 ∞ 随伴の写像空間比較の具体的入力。
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
  (cofC : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (cofD : MorphismProperty.FunctorialFactorizationData (cofibrations D) (trivialFibrations D))
  (fibD : MorphismProperty.FunctorialFactorizationData (trivialCofibrations D) (fibrations D))
variable {R : D ⥤ C} (adj : L ⊣ R)
local notation "qC" => cosimplicialResolutionFamily cofC
local notation "qD" => cosimplicialResolutionFamily cofD
local notation "P" => CosimplicialFrameFamily.ofResolution qC
local notation "Q" => cofibrantSource cofC
local notation "ε" => cofibrantSourceComparison cofC
local notation "RD" => fibrantTarget fibD
local notation "W" => Functor.obj (Functor.whiskeringLeft D D SSet) RD

/-- 元の因子分解で構成した、左右の標準導来 Hom と共通する Kan Hom の二変数関手。 -/
abbrev chosenQuillenDerivedHomMiddle : Cᵒᵖ ⥤ D ⥤ SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenDerivedHomMiddle L P Q cofD qD fibD

/-- 左側 LQ の元の標準解消 Hom から共通 Hom への同じ自然変換。 -/
def chosenQuillenDerivedHomFromLeft :
    FrameOverFunctor.hom (FrameOverFunctor.resolution qD (Q ⋙ L)) ⋙ W ⟶
      chosenQuillenDerivedHomMiddle L cofC cofD fibD :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenDerivedHomFromLeft L P Q cofD qD fibD

/-- 右側 X の元の標準解消 Hom から、元の始域比較と随伴比較を通る同じ自然変換。 -/
def chosenQuillenDerivedHomFromRight :
    Functor.op (CofibrantResolutionFamily.obj qC) ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙
      (Functor.whiskeringLeft D C SSet.{u}).obj (RD ⋙ R) ⟶
        chosenQuillenDerivedHomMiddle L cofC cofD fibD :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionHomSourceRestriction qC Q ε (RD ⋙ R) ≫
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenDerivedHomFromRight L P Q cofD qD fibD adj

/-- 左側の標準導来 Hom からの元の自然変換は、各パラメータでホモトピー同値。 -/
lemma chosenQuillenDerivedHomFromLeft_homotopyEquivalence (X : Cᵒᵖ) (Y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (((chosenQuillenDerivedHomFromLeft L cofC cofD fibD).app X).app Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenDerivedHomFromLeft_homotopyEquivalence L P Q (cofibrantSource_isCofibrant cofC)
    cofD qD fibD X Y

include adj in
/-- 右側 X の標準導来 Hom からの元の自然変換も、全パラメータでホモトピー同値。 -/
lemma chosenQuillenDerivedHomFromRight_homotopyEquivalence (X : Cᵒᵖ) (Y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (((chosenQuillenDerivedHomFromRight L cofC cofD fibD adj).app X).app Y) := by
  have ht := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenReplacedFrame_rightTarget_isFibrant adj fibD Y
  have : IsFibrant ((RD ⋙ R).obj Y) := ht
  have : KanComplex
      ((((qC).obj.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙
        (Functor.whiskeringLeft D C SSet).obj (RD ⋙ R)).obj X).obj Y) :=
    cosimplicialHom_kanComplex _ ((qC).cofibrant X.unop)
      ((qC).atObject X.unop).homotopicallyConstant (R.obj ((RD).obj Y))
  have : KanComplex
      (((((Q ⋙ (qC).obj).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙
        (Functor.whiskeringLeft D C SSet).obj (RD ⋙ R))).obj X).obj Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenReplacedFrame_rightHom_kanComplex adj P Q fibD X Y
  have := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenDerivedHomMiddle_kanComplex L P Q (cofibrantSource_isCofibrant cofC)
    cofD qD fibD X Y
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
    ((((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionHomSourceRestriction qC Q ε (RD ⋙ R)).app X).app Y) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenDerivedHomFromRight L P Q cofD qD fibD adj).app X).app Y)
  exact (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionHomSourceRestriction_homotopyEquivalence qC Q ε (RD ⋙ R)
    (fun X ↦ (cofibrantSourceComparison_trivialFibration cofC X).2) X Y).comp
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenDerivedHomFromRight_homotopyEquivalence L P Q (cofibrantSource_isCofibrant cofC)
        cofD qD fibD adj X Y)

variable
  (fibC : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- 右導来像 RRY から、その同じ元の標準写像空間の終域置換へ至る自然変換。 -/
def chosenQuillenRightTargetReplacement :
    Functor.op (CofibrantResolutionFamily.obj qC) ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙
      (Functor.whiskeringLeft D C SSet.{u}).obj (RD ⋙ R) ⟶
        chosenResolutionHom cofC fibC ⋙ (Functor.whiskeringLeft D C SSet.{u}).obj (RD ⋙ R) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionHomTargetReplacement qC (RD ⋙ R) fibC

include adj in
/-- 元の右導来像は fibrant なので、標準写像空間への同じ比較もホモトピー同値。 -/
lemma chosenQuillenRightTargetReplacement_homotopyEquivalence (X : Cᵒᵖ) (Y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (((chosenQuillenRightTargetReplacement (R := R) cofC fibD fibC).app X).app Y) := by
  have : IsFibrant ((RD ⋙ R).obj Y) := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenReplacedFrame_rightTarget_isFibrant adj fibD Y
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionHomTargetReplacement_homotopyEquivalence qC (RD ⋙ R) fibC X Y

end
end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
