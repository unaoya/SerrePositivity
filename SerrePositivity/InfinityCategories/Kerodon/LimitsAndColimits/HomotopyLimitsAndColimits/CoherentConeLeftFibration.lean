module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.PullbackSections
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningFiberIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceModelEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEquivalence

/-!
概要：coherent な錐の切断模型を図式上の left fibration とその写像空間の fiber で表示する。
方針：頂点の coslice 射影を図式に沿って引き戻し、既存の fiber 比較を適用する。
規約：fiber ごとの比較と、係数図式の全体の比較を区別する。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の表現可能な切断模型。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {K X : SSet.{u}}

/-- 概要：頂点 x の coslice を図式 p に沿って引き戻した全空間。
方針：coslice 射影と図式の引き戻しを取る。
規約：底は図式の始域 K。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の錐の表現可能な left fibration。 -/
noncomputable def coherentConeTotal (p : K ⟶ X) (x : X _⦋0⦌) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) p

/-- 概要：coherent な錐の全空間から図式の始域への射影。
方針：coslice の引き戻しの第二射影を取る。
規約：元の単体集合の充填性は射の定義には不要。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断が錐を表す射影。 -/
noncomputable def coherentConeProjection (p : K ⟶ X) (x : X _⦋0⦌) :
    coherentConeTotal p x ⟶ K :=
  pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) p

/-- 概要：quasicategory 内の図式に沿って制限した coslice 射影は left fibration。
方針：coslice 射影の left fibration 性を引き戻す。
規約：K 自身の quasicategory 性は不要。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の空間値の表現可能な図式の模型。 -/
instance coherentConeProjection_leftFibration [Quasicategory X] (p : K ⟶ X)
    (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (coherentConeProjection p x) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) p
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem⟩

/-- 概要：錐の left fibration の切断空間は coslice の相対関手による錐の模型と同型。
方針：引き戻しの切断と相対関手空間の普遍的な同型を使う。
規約：同型の定義には quasicategory 性を要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の実際の錐の切断模型。 -/
noncomputable def coherentConeSectionsIso (p : K ⟶ X) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (coherentConeProjection p x) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.pullbackSectionsRelativeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) p

/-- 概要：錐の left fibration の頂点 fiber は元の coslice の対応する fiber と同型。
方針：引き戻しの fiber の同型を適用する。
規約：底の頂点は図式 p の零次成分で写す。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の係数値の回収。 -/
noncomputable def coherentConeProjectionFiberIso (p : K ⟶ X) (x : X _⦋0⦌) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (coherentConeProjection p x) k ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x))
        (p.app (Opposite.op ⦋0⦌) k) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) p k

/-- 概要：錐の left fibration の各 fiber は始点 x と図式の値との右 pinched 写像空間に同値。
方針：coslice の fiber の同型と F1 の左右の写像空間の比較を合成する。
規約：同値の逆の選択を含み、図式全体の自然変換をまだ主張しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の表現可能な係数の点ごとの比較。 -/
noncomputable def coherentConeProjectionMappingEquivalence [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (coherentConeProjection p x) k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x (p.app (Opposite.op ⦋0⦌) k)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (coherentConeProjectionFiberIso p x k)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberRightMappingEquivalence x (p.app (Opposite.op ⦋0⦌) k))

/-- 概要：各 coherent な錐は対応する left fibration の切断空間の具体的な点を与える。
方針：相対関手空間に作った錐の点を切断空間の同型の逆で移す。
規約：元の錐は任意の join の錐でよい。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の比較ファイバーの底のデータ。 -/
noncomputable def coherentConeSectionVertex {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (coherentConeProjection p c.vertex)) _⦋0⦌ :=
  (coherentConeSectionsIso p c.vertex).inv.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionPoint c)

/-- 概要：局所 Kan な単体的圏の錐の left fibration の各 fiber は豊穣 Hom の模型に同値。
方針：右 pinched 写像空間への比較と F1 の豊穣 Hom 比較の逆を合成する。
規約：図式の値の頂点との等式を明示し、Hom の宇宙の持ち上げを省略しない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の実際の豊穣 Hom の点ごとの回収。 -/
noncomputable def coherentConeProjectionHomEquivalence
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {K : SSet.{max u v}} (p : K ⟶ SimplicialNerve C) (x y : C) (k : K _⦋0⦌)
    (hy : p.app (Opposite.op ⦋0⦌) k = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (coherentConeProjection p (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) k)
      ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x y)) :=
  (coherentConeProjectionMappingEquivalence p (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) k).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) hy))).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomEquivalence x y).symm)

/-- 概要：通常の strict な図式上の錐の left fibration の fiber は実際の豊穣 Hom に同値。
方針：標準の coherent 表示の頂点の計算を、一般の fiber の Hom 比較へ渡す。
規約：添字圏の nerve の持ち上げと Hom の持ち上げを両方明示する。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の strict な Hom 図式との比較の入力。 -/
noncomputable def strictCoherentConeFiberHomEquivalence
    {J : Type u} [SmallCategory J] {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    (F : J ⥤ C) (x : C) (i : J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
      (coherentConeProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x))
        (ULift.up (ComposableArrows.mk₀ i)))
      ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x (F.obj i))) :=
  coherentConeProjectionHomEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) x (F.obj i)
    (ULift.up (ComposableArrows.mk₀ i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex F i)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
