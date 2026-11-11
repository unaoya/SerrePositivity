module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConstantFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.RightHomotopySquare
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan

/-!
概要：ホモトピー圏の射による区間写像空間への前後合成作用。
方針：普遍族の h Fun での合成を代表する族を選び、パラメータ自然性で特徴づける。
規約：射の選択による任意性は実際の単体的ホモトピーで比較する。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の対象変数に関する自然性。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：hX の射による区間写像空間への前合成。
方針：定値二胞体と恒等族の合成を代表する族を選ぶ。
規約：X は quasicategory。厳密な結合則は要求しない。
使われ方：随伴比較の始域変数の自然性。 -/
noncomputable def intervalPrecompose {X : SSet.{u}} [Quasicategory X]
    {x' x : X _⦋0⦌} (y : X _⦋0⦌)
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x' y :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_surjective _ X x' y
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap _ γ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (𝟙 _)))

/-- 概要：選んだ前合成射が表す普遍族の合成。
方針：代表の選択の仕様を読む。
規約：intervalPrecompose の同じ射を使う。
使われ方：任意のパラメータでの公式。 -/
lemma intervalPrecompose_hom {X : SSet.{u}} [Quasicategory X]
    {x' x : X _⦋0⦌} (y : X _⦋0⦌)
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (intervalPrecompose y γ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap _ γ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (𝟙 _) :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_surjective _ X x' y
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap _ γ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (𝟙 _)))

/-- 概要：前合成は任意のパラメータ族で h Fun の合成を表す。
方針：普遍族での仕様と定値二胞体のパラメータ自然性を使う。
規約：パラメータ A は任意の単体集合。
使われ方：前合成の選択独立性と対象自然性の計算。 -/
lemma intervalPrecompose_family {A X : SSet.{u}} [Quasicategory X]
    {x' x y : X _⦋0⦌}
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ intervalPrecompose y γ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A γ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom f := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_precomp, intervalPrecompose_hom]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp, Functor.map_comp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp f (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap _ γ) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (𝟙 _)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_precomp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_precomp, Category.comp_id]

/-- 概要：hX の射による区間写像空間への後合成。
方針：恒等族と定値二胞体の合成を代表する族を選ぶ。
規約：X は quasicategory。
使われ方：随伴比較の終域変数の自然性。 -/
noncomputable def intervalPostcompose {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) {y y' : X _⦋0⦌}
    (δ : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y' :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_surjective _ X x y'
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (𝟙 _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap _ δ))

/-- 概要：選んだ後合成射が表す普遍族の合成。
方針：代表の選択の仕様を読む。
規約：intervalPostcompose の同じ射を使う。
使われ方：任意のパラメータでの公式。 -/
lemma intervalPostcompose_hom {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) {y y' : X _⦋0⦌}
    (δ : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (intervalPostcompose x δ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (𝟙 _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap _ δ :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_surjective _ X x y'
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (𝟙 _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap _ δ))

/-- 概要：後合成は任意のパラメータ族で h Fun の合成を表す。
方針：普遍族での仕様と定値二胞体のパラメータ自然性を使う。
規約：パラメータ A は任意の単体集合。
使われ方：後合成の選択独立性と対象自然性の計算。 -/
lemma intervalPostcompose_family {A X : SSet.{u}} [Quasicategory X]
    {x y y' : X _⦋0⦌}
    (δ : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk y')
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ intervalPostcompose x δ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A δ := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_precomp, intervalPostcompose_hom]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp, Functor.map_comp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (𝟙 _)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp f (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap _ δ) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_precomp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_precomp, Category.comp_id]

/-- 概要：恒等射による前合成は恒等写像にホモトピック。
方針：普遍族の表示と定値二胞体の恒等則を使う。
規約：実際の単体的ホモトピーを返す。
使われ方：対象変数の恒等則。 -/
lemma intervalPrecompose_id {X : SSet.{u}} [Quasicategory X] (x y : X _⦋0⦌) :
    Nonempty (SSet.Homotopy (intervalPrecompose y (𝟙 (HomotopyCategory.mk x))) (𝟙 _)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_eq_imp_homotopy
  rw [intervalPrecompose_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_id, Category.id_comp]

/-- 概要：恒等射による後合成は恒等写像にホモトピック。
方針：普遍族の表示と定値二胞体の恒等則を使う。
規約：実際の単体的ホモトピーを返す。
使われ方：対象変数の恒等則。 -/
lemma intervalPostcompose_id {X : SSet.{u}} [Quasicategory X] (x y : X _⦋0⦌) :
    Nonempty (SSet.Homotopy (intervalPostcompose x (𝟙 (HomotopyCategory.mk y))) (𝟙 _)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_eq_imp_homotopy
  rw [intervalPostcompose_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_id, Category.comp_id]

/-- 概要：前合成作用は合成則をホモトピーまで満たす。
方針：族の公式と h Fun の合成の結合則を使う。
規約：始域変数に反変な順序で合成する。
使われ方：写像空間の対象作用の合成則。 -/
lemma intervalPrecompose_comp {X : SSet.{u}} [Quasicategory X]
    {x'' x' x : X _⦋0⦌} (y : X _⦋0⦌)
    (γ' : (HomotopyCategory.mk x'' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x')
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x) :
    Nonempty (SSet.Homotopy (intervalPrecompose y γ ≫ intervalPrecompose y γ')
      (intervalPrecompose y (γ' ≫ γ))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_eq_imp_homotopy
  rw [intervalPrecompose_family, intervalPrecompose_hom, intervalPrecompose_hom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_comp, Category.assoc]

/-- 概要：後合成作用は合成則をホモトピーまで満たす。
方針：族の公式と h Fun の合成の結合則を使う。
規約：終域変数に共変な順序で合成する。
使われ方：写像空間の対象作用の合成則。 -/
lemma intervalPostcompose_comp {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) {y y' y'' : X _⦋0⦌}
    (δ : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk y')
    (δ' : (HomotopyCategory.mk y' : hoFunctor.obj X) ⟶ HomotopyCategory.mk y'') :
    Nonempty (SSet.Homotopy (intervalPostcompose x δ ≫ intervalPostcompose x δ')
      (intervalPostcompose x (δ ≫ δ'))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_eq_imp_homotopy
  rw [intervalPostcompose_family, intervalPostcompose_hom, intervalPostcompose_hom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_comp, Category.assoc]

/-- 概要：前合成と後合成はホモトピーまで可換。
方針：両経路の族の表示を合成の結合則で比較する。
規約：二つの対象変数の射は任意の hX の射。
使われ方：二変数の写像空間作用の整合。 -/
lemma intervalPrecompose_postcompose {X : SSet.{u}} [Quasicategory X]
    {x' x y y' : X _⦋0⦌}
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x)
    (δ : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk y') :
    Nonempty (SSet.Homotopy (intervalPrecompose y γ ≫ intervalPostcompose x' δ)
      (intervalPostcompose x δ ≫ intervalPrecompose y' γ)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_eq_imp_homotopy
  rw [intervalPostcompose_family, intervalPrecompose_family,
    intervalPrecompose_hom, intervalPostcompose_hom, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
