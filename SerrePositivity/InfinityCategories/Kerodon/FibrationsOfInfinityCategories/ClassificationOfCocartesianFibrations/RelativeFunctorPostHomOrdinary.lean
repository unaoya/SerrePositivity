module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorEnrichedEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPostcomposition

/-!
概要：相対 Hom の豊穣後合成と通常の底を保つ射による後合成の整合性。
方針：通常の射の豊穣表示を代入して uncurry し、相対関手の値を計算する。
規約：通常の後合成には F2 の既存の relativeFunctorPost を使う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、straightening の辺への作用の計算。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：通常の底上の射の相対 Hom での表示を豊穣後合成で評価すると通常の後合成になる。
方針：内部 Hom の単位からの射を uncurry し、各次数の相対関手の値を比較する。
規約：a、b、c の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、豊穣評価と既存の相対後合成の接続。 -/
lemma relativeFunctorPostHom_ordinary {B : SSet.{u}} (a b c : Over B) (f : b ⟶ c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv b c f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPostHom a b c =
      curry' (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost b.hom c.hom f.left f.w a.hom) := by
  apply uncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPostHom, uncurry_natural_left, uncurry_curry, curry', uncurry_curry]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom a.left).map c.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a.hom)
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_ι,
    whiskerLeft_comp_tensorHom_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv_ι,
    tensorHom_def_assoc, whiskerLeft_curry'_comp]
  erw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost_ι]
  simp only [rightUnitor_naturality_assoc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
