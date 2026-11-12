module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanPointHomNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictKanUnstraighteningComparison

/-!
概要：反転した Kan 値図式の一点からの豊穣係数を二重反転で元の係数へ戻す。
方針：一点からの Hom の自然同型を反転し、単体集合の二重反転の自然同型を合成する。
規約：最初の反転は Kan 値図式の値に施し、底の圏は変えない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、weighted nerve から coherent な復元への係数比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：Kan 複体の反転を通常の Kan 複体の圏の関手とする。
方針：単体集合の反転関手を対象と射に適用し、Kan 性の反転での保存を使う。
規約：通常の射の向きは変えず、単体の頂点順序を反転する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な復元比較の図式の規約の調整。 -/
def kanObjectOpFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj K := ⟨K.obj.op, inferInstance⟩
  map f := SSet.opFunctor.map f
  map_id K := SSet.opFunctor.map_id K.obj
  map_comp f g := SSet.opFunctor.map_comp f g

/-- 概要：反転した図式の一点からの反転豊穣係数は、元の Kan 値図式の単体集合と自然同型。
方針：一点からの Hom の自然同型を反転し、二重反転を消去する。
規約：coherent 図式には反転した Kan 値図式を使い、weighted nerve の係数には元の図式を得る。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict transport の元の係数による全空間比較。 -/
noncomputable def oppositePointHomDiagramIso
    {C : Type u} [Category.{u} C] (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (F ⋙ kanObjectOpFunctor) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject ⋙
      SSet.opFunctor) ≅ F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget := by
  let e := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (F ⋙ kanObjectOpFunctor) _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.pointKanObjectHomNatIso) SSet.opFunctor
  exact e ≪≫ Functor.isoWhiskerLeft (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) SSet.opFunctorCompOpFunctorIso

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
