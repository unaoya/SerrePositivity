module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransportDiagramMixedHom

/-!
概要：底の射列と coherent な strict transport 図式の対角評価。
方針：順向きの Hom は元の core の混合作用を使い、逆向きは空の path から写す。
規約：全高次の変換を保持した QCat 値の評価を構成する。
使われ方：Cat∞ 値関手への実現の各単体。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：底の図式と coherent な strict transport の同じ添字を評価する。
方針：図式の対応する対象で quasicategoryの値を取る。
規約：通常の図式 A は順序 J を始域とする。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、対角 coherent 図式の対象の作用。 -/
def diagonalCocartesianTransportDiagramObject {C : Type u} [Category.{u} C] {J : Type u}
  [LinearOrder J]
    (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C))
    (i : SimplicialThickening J) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue (F.obj i) (A.obj i.as)

/-- 概要：対角評価の二対象間の豊穣 Hom の作用。
方針：順向きでは strict な変換空間を混合作用で写し、逆向きでは path の不存在を使う。
規約：順序の証明の選択は射を変えない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、対角 coherent 図式の Hom の作用。 -/
noncomputable def diagonalCocartesianTransportDiagramHom {C : Type u} [Category.{u} C] {J : Type
  u} [LinearOrder J]
    (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C))
    (i j : SimplicialThickening J) :
    SimplicialCategory.sHom i j ⟶
      SimplicialCategory.sHom (diagonalCocartesianTransportDiagramObject A F i)
        (diagonalCocartesianTransportDiagramObject A F j) :=
  if h : i.as ≤ j.as then
    F.map i j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramMixedHom (A.map (homOfLE h))
      (F.obj i) (F.obj j)
  else
    { app n := ↾fun P ↦ (h (SimplicialThickening.Path.le (P.obj 0))).elim
      naturality {n m} α := by
        apply ConcreteCategory.hom_ext
        intro P
        exact (h (SimplicialThickening.Path.le (P.obj 0))).elim }

/-- 概要：端点が順方向なら対角評価の Hom は混合作用の式に一致する。
方針：順序による分岐の肯定側を計算する。
規約：h の証明は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、対角評価の単位則と合成則の検証。 -/
lemma diagonalCocartesianTransportDiagramHom_of_le {C : Type u} [Category.{u} C] {J : Type u}
  [LinearOrder J]
    (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C))
    (i j : SimplicialThickening J) (h : i.as ≤ j.as) :
    diagonalCocartesianTransportDiagramHom A F i j =
      F.map i j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramMixedHom (A.map (homOfLE h))
      (F.obj i) (F.obj j) :=
  dite_eq_left h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
