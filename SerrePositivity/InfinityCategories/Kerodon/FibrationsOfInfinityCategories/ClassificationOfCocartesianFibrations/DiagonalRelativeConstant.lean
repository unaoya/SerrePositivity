module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.DiagonalRelativeEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorMixedUnit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ConstantOrderDiagram
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
概要：fibration のパラメーターを固定した対角相対評価の通常の図式による表示。
方針：反変な底上の図式の相対 Hom を通常の Kan 値関手とし、混合作用の単位で比較する。
規約：底の図式の対象は動かし、標的の fibration は固定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な straightening の頂点での値の同定。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：底上の反変図式から固定した left fibration への相対 Hom は通常の Kan 値図式をなす。
方針：底上の射による前合成を各関手空間の射とし、二つの反変性を合成する。
規約：標的の fibration p は束縛した対象。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な対角評価の通常の図式での表示。 -/
def relativeFunctorKanDiagram {B : SSet.{u}} {J : Type u} [Category.{u} J]
    (A : Jᵒᵖ ⥤ Over B) (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj i := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p.val.hom (A.obj (Opposite.op i)).hom, inferInstance⟩
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p.val.hom (A.map f.op)
  map_id i := by
    rw [show A.map (𝟙 i).op = 𝟙 _ from A.map_id _, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_id]
    rfl
  map_comp f g := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p.val.hom (A.map (g.op ≫ f.op)) = _
    rw [A.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_comp]
    rfl

/-- 概要：定値な fibration の図式による対角評価は相対 Hom の通常の関手の coherent 表示に一致する。
方針：各 Hom の単体で順序を取り出し、恒等射における混合作用を通常の前合成へ戻す。
規約：J は任意の線形順序。局所 Kan 性を追加の仮定にしない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類関手を fibration の頂点で評価する計算。 -/
lemma diagonalRelativeEvaluation_constant {B : SSet.{u}} {J : Type u} [LinearOrder J]
    (A : Jᵒᵖ ⥤ Over B) (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalRelativeEvaluation A (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.enrichedConstantOrderDiagram J p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram (relativeFunctorKanDiagram A p) := by
  refine EnrichedFunctor.ext SSet
    (F := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalRelativeEvaluation A (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.enrichedConstantOrderDiagram J p))
    (G := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram (relativeFunctorKanDiagram A p)) (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  have hij : i.as ≤ j.as := SimplicialThickening.Path.le (P.obj 0)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalRelativeHom A (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.enrichedConstantOrderDiagram J p) i j).app d P = _
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalRelativeHom_of_le A (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.enrichedConstantOrderDiagram J p) i j hij]
  change ((toUnit _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity p.val ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorMixedHom (A.map (homOfLE hij).op) p.val p.val).app d) P =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p.val.hom (A.map (homOfLE hij).op))) d.unop.len
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorMixedHom_unit]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.unitHom_app_constant (curry' (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p.val.hom (A.map (homOfLE hij).op)))
    d.unop.len

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
