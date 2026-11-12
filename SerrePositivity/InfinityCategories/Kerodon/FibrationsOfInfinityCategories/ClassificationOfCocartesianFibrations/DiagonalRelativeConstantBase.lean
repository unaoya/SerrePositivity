module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.DiagonalRelativeEvaluation

/-!
概要：対角相対評価の反変な底上の図式を定値に固定したときの計算。
方針：定義域の恒等による前合成を消去し、豊穣後合成の評価へ戻す。
規約：fibration の coherent パラメーターは任意に動かす。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、straightening の対象ごとの高次の評価。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：定義域の恒等射での混合 Hom は豊穣後合成と一致する。
方針：底上の前合成の恒等則と内部 Hom の恒等則を使う。
規約：標的の二つの底上の対象 p と q は独立に動かす。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、底の対象を固定した共同評価。 -/
lemma relativeFunctorMixedHom_domain_id {B : SSet.{u}} (a p q : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorMixedHom (𝟙 a) p q = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPostHom a p q := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorMixedHom, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_id,
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p.hom a.hom)).map_id, Category.comp_id]

/-- 概要：底上の定値図式の対角評価は固定した対象からの豊穣相対 Hom の評価になる。
方針：path の端点の順序を使い、混合 Hom の定義域の恒等を消去する。
規約：任意の線形順序 J と coherent な fibration の図式 F を扱う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、共同評価の底の対象への制限。 -/
lemma diagonalRelativeEvaluation_constant_base
    {B : SSet.{u}} {J : Type u} [LinearOrder J] (a : Over B)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalRelativeEvaluation ((Functor.const Jᵒᵖ).obj a) F =
      F.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation a) := by
  refine EnrichedFunctor.ext SSet
    (F := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalRelativeEvaluation ((Functor.const Jᵒᵖ).obj a) F)
    (G := F.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation a)) (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalRelativeHom ((Functor.const Jᵒᵖ).obj a) F i j).app d P = _
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalRelativeHom_of_le _ F i j (SimplicialThickening.Path.le (P.obj 0))]
  change ((F.map i j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorMixedHom (𝟙 a) (F.obj i).val (F.obj j).val).app d) P = _
  rw [relativeFunctorMixedHom_domain_id]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
