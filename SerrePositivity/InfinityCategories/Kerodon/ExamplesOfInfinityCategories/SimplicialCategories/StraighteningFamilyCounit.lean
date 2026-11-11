module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallFiberStraighteningCounit

/-!
概要：図式の族の再構成を全パラメーターで同時に元の族と比較する。
方針：積の底上の余単位を内部 currying で関手単体集合の同型へ移す。
規約：点ごとの表現を独立に選ばず、一つの族全体の表現を使う。
使われ方：普遍図式の再構成と恒等関手との coherent な比較。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：積の底上の図式同型は curry した族全体の同型となる。
方針：内部 currying の同型により同じ頂点同型を写す。
規約：始域は任意で標的の追加仮定は不要。
使われ方：分類図式の余単位を全パラメーターで束ねる。 -/
def coherentFamilyCurryIso {A B X : SSet.{u}} {f g : A ⊗ B ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (curry f) (curry g) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (ihomCurryIso A B X).hom

/-- 概要：任意の coherent な族の分類による再構成は元の族と関手同型。
方針：積の底上の一つの余単位を curry する。
規約：パラメーターの各次数の小ささを要求しない。
使われ方：高次の全パラメーターを含む図式の族の比較。 -/
def coherentStraighteningFamilyCounit {B K : SSet.{u + 1}}
    (F : B ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallFiberLeftStraighteningDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.leftUnstraighteningProjection_hasSmallSimplexFibers F))) (curry F) :=
  coherentFamilyCurryIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentStraighteningCounit F)

/-- 概要：全図式の普遍族の再構成を関手単体集合の自己写像にする。
方針：評価図式の unstraightening を族全体として分類して curry する。
規約：これは普遍族の再構成であり点ごとの選択の集合ではない。
使われ方：全図式にわたる coherent な比較の始域。 -/
def universalCoherentReconstructionMap (B : SSet.{u + 1}) :
    (ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} ⟶ (ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  curry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallFiberLeftStraighteningDiagram
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (uncurry (𝟙 ((ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.leftUnstraighteningProjection_hasSmallSimplexFibers _))

/-- 概要：全図式の普遍族の再構成は恒等関手と関手同型。
方針：普遍族への余単位と curry・uncurry の往復を使う。
規約：全図式・非可逆変換・高次単体を一度に比較する。
使われ方：対象ごとの余単位から全図式の比較へ進む界面。 -/
def universalCoherentReconstructionCounitIso (B : SSet.{u + 1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (universalCoherentReconstructionMap B) (𝟙 ((ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})) :=
  coherentStraighteningFamilyCounit (uncurry (𝟙 ((ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))) ≪≫
    eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d))
      (curry_uncurry (𝟙 ((ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
