module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorAnodyneRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorUnitHom
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：底と部分図式を固定する相対関手の延長の選択空間。
方針：相対関手空間の制限の指定した頂点上の fiber を取る。
規約：left anodyne な制限では、全高次の選択を含む可縮な Kan 複体となる。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、unstraightening の相対的な持ち上げの高次の整合性。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：底 b と部分図式 v を厳密に固定した相対関手の延長の単体集合。
方針：相対制限の v の相対頂点上の fiber を取る。
規約：射影 p の充填性は定義には不要。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、境界付きの相対表現の延長の選択空間。 -/
@[kerodon 01AB]
def relativeFunctorExtensionSpace {A D E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A)
    (v : D ⟶ E) (hv : v ≫ p = i ≫ b) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p b i) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ b) v hv)

/-- 概要：相対延長の選択空間から底を保つ図式の空間への包含。
方針：相対制限の fiber の包含を取る。
規約：固定した部分図式の条件だけを忘れる。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、持ち上げの族の頂点での評価。 -/
def relativeFunctorExtensionSpaceι {A D E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A)
    (v : D ⟶ E) (hv : v ≫ p = i ≫ b) :
    relativeFunctorExtensionSpace p b i v hv ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p b i) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ b) v hv)

/-- 概要：相対延長の族を部分図式へ制限すると指定した部分図式に定値となる。
方針：fiber の包含の底への合成を計算する。
規約：選択空間全体からの射の等式。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、延長の族が部分図式を厳密に固定する条件。 -/
lemma relativeFunctorExtensionSpaceι_pre {A D E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A)
    (v : D ⟶ E) (hv : v ≫ p = i ≫ b) :
    relativeFunctorExtensionSpaceι p b i v hv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p b i =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ b) v hv) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp _ _

/-- 概要：left anodyne な部分図式の相対延長の選択空間は可縮な Kan 複体。
方針：相対制限の全境界持ち上げと、その fiber の可縮性を使う。
規約：底 B と図式の定義域 A、D の quasicategory 性は不要。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、相対持ち上げの全高次の一意性。 -/
lemma relativeFunctorExtensionSpace_isContractibleKan {A D E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : A ⟶ B) (i : D ⟶ A)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (relativeFunctorExtensionSpace p b i v hv) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_trivialKanFibration p b i hi
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan _ _

/-- 概要：相対延長の選択空間の頂点は、底と部分図式を保つ実際の延長と全単射に対応する。
方針：相対関手の頂点の全単射を、制限が指定図式となる条件へ制限する。
規約：延長と底上の可換性は厳密な等式で表す。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、抽象的な可縮性と実際の延長との接続。 -/
noncomputable def relativeFunctorExtensionSpaceVertexEquiv {A D E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A)
    (v : D ⟶ E) (hv : v ≫ p = i ≫ b) :
    {W : A ⟶ E // W ≫ p = b ∧ i ≫ W = v} ≃
      (relativeFunctorExtensionSpace p b i v hv) _⦋0⦌ where
  toFun W := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p b W.val W.property.1, by
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ W.val) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v
    exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex W.property.2⟩
  invFun s := by
    let W := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv p b).symm s.val
    refine ⟨W.val, W.property, ?_⟩
    have hW : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p b W.val W.property = s.val :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv p b).apply_symm_apply s.val
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
    have hs := congrArg Subtype.val s.property
    change ((pre i).app E).app (Opposite.op ⦋0⦌) s.val.val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v at hs
    have hh := congrArg (fun z => ((pre i).app E).app (Opposite.op ⦋0⦌) z.val) hW
    exact hh.trans hs
  left_inv W := by
    apply Subtype.ext
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv p b).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p b W.val W.property.1)).val = W.val
    exact congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv p b).symm_apply_apply
      ⟨W.val, W.property.1⟩)
  right_inv s := by
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv p b).apply_symm_apply s.val

/-- 概要：left anodyne な部分図式上で指定された相対図式は実際に延長できる。
方針：可縮な延長空間の頂点を、実際の延長への全単射で戻す。
規約：底 b と部分図式 v の双方を厳密に保つ。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、パラメーター付き unstraightening の持ち上げの存在。 -/
lemma exists_relativeFunctorExtension_of_leftAnodyne {A D E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : A ⟶ B) (i : D ⟶ A)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ b) :
    ∃ W : A ⟶ E, W ≫ p = b ∧ i ≫ W = v := by
  obtain ⟨x⟩ := (relativeFunctorExtensionSpace_isContractibleKan p b i hi v hv).nonempty
  let W := (relativeFunctorExtensionSpaceVertexEquiv p b i v hv).symm x
  exact ⟨W.val, W.property⟩

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
