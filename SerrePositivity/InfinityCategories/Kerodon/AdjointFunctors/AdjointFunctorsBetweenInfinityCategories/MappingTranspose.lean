module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.MappingParameters

/-!
概要：関手単体集合の写像空間の族の転置。
方針：区間を展開し、パラメータ A と区間を交換して uncurry する。
規約：straightening に依存せず、quasicategory 性も要求しない。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1）、写像空間の族を h Fun の射で計算する比較。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：区間と第一パラメータを入れ替える。
方針：結合子と対称性を合成する。
規約：第二パラメータ B はそのまま保つ。
使われ方：区間の族の転置の定義。 -/
def intervalParameterSwap (A B : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (A ⊗ B) ⟶ A ⊗ (Δ[1] ⊗ B) :=
  (α_ Δ[1] A B).inv ≫ ((β_ (Δ[1] : SSet.{u}) A).hom ▷ B) ≫ (α_ A Δ[1] B).hom

/-- 概要：区間とパラメータの交換は端点と整合する。
方針：次数ごとに成分を計算する。
規約：両方の端点 i を扱う。
使われ方：転置した族の端点条件。 -/
lemma intervalParameterSwap_endpoint (A B : SSet.{u}) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (A ⊗ B) ≫ intervalParameterSwap A B = A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i B := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 概要：関手単体集合の区間族を元の単体集合の二重パラメータ族へ展開する。
方針：区間を展開し、A を評価の変数として uncurry する。
規約：定値関手を両端に持つ族。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の写像空間の族の比較。 -/
def intervalTransposeUncurry {A B X : SSet.{u}} {x y : X _⦋0⦌}
    (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y))) : (Δ[1] : SSet.{u}) ⊗ (A ⊗ B) ⟶ X :=
  intervalParameterSwap A B ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f)

/-- 概要：展開して転置した族の零端点は元の始点に定値。
方針：端点と交換の整合、uncurry の自然性、定値関手の評価を使う。
規約：A と B は任意の単体集合。
使われ方：転置した族を区間写像空間へ戻す端点条件。 -/
lemma intervalTransposeUncurry_zero {A B X : SSet.{u}} {x y : X _⦋0⦌}
    (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (A ⊗ B) ≫ intervalTransposeUncurry f = SSet.const x := by
  unfold intervalTransposeUncurry
  rw [← Category.assoc, intervalParameterSwap_endpoint, ← uncurry_natural_left,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex, SSet.comp_const]

/-- 概要：展開して転置した族の一端点は元の終点に定値。
方針：零端点と同じ閉構造の計算を時刻一で使う。
規約：A と B は任意の単体集合。
使われ方：転置した族を区間写像空間へ戻す端点条件。 -/
lemma intervalTransposeUncurry_one {A B X : SSet.{u}} {x y : X _⦋0⦌}
    (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (A ⊗ B) ≫ intervalTransposeUncurry f = SSet.const y := by
  unfold intervalTransposeUncurry
  rw [← Category.assoc, intervalParameterSwap_endpoint, ← uncurry_natural_left,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_one, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex, SSet.comp_const]

/-- 概要：Fun(A,X) の定値関手間の写像空間の族を、X の写像空間への A×B 族へ転置する。
方針：転置した区間の族を端点条件とともに curry する。
規約：ここでは商やホモトピー同値は主張しない。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1）、h Fun の射の等式から族のホモトピーを作る準備。 -/
noncomputable def intervalFamilyTranspose {A B X : SSet.{u}} {x y : X _⦋0⦌}
    (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y))) : A ⊗ B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyCurry (intervalTransposeUncurry f)
    (intervalTransposeUncurry_zero f) (intervalTransposeUncurry_one f)

/-- 概要：転置した族の区間への展開は定義した二重パラメータ族。
方針：端点指定の curry の往復を使う。
規約：証明の選択に依存しない。
使われ方：転置の自然性とホモトピー端点の計算。 -/
lemma intervalFamilyTranspose_uncurry {A B X : SSet.{u}} {x y : X _⦋0⦌}
    (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (intervalFamilyTranspose f) = intervalTransposeUncurry f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyUncurry_curry _ _ _

/-- 概要：区間とパラメータの交換は第二パラメータの射に自然。
方針：成分の順序を次数ごとに計算する。
規約：第一パラメータ A と区間は固定。
使われ方：転置のパラメータ自然性。 -/
lemma intervalParameterSwap_naturality {B C : SSet.{u}} (A : SSet.{u}) (i : B ⟶ C) :
    (Δ[1] ◁ (A ◁ i)) ≫ intervalParameterSwap A C =
      intervalParameterSwap A B ≫ (A ◁ (Δ[1] ◁ i)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 概要：展開した転置は第二パラメータの前合成と整合する。
方針：区間模型の自然性、uncurry の自然性、交換の自然性を使う。
規約：パラメータの射 i に条件は課さない。
使われ方：転置したホモトピーの端点の計算。 -/
lemma intervalTransposeUncurry_precomp {A B C X : SSet.{u}} {x y : X _⦋0⦌}
    (i : B ⟶ C)
    (f : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y))) :
    intervalTransposeUncurry (i ≫ f) =
      (Δ[1] ◁ (A ◁ i)) ≫ intervalTransposeUncurry f := by
  unfold intervalTransposeUncurry
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, uncurry_natural_left,
    ← Category.assoc, ← intervalParameterSwap_naturality, Category.assoc]

/-- 概要：区間写像空間の族の転置は第二パラメータに自然。
方針：区間への展開の単射性で比較する。
規約：前合成する射 i は任意。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の族のホモトピーを端点で制限する計算。 -/
lemma intervalFamilyTranspose_precomp {A B C X : SSet.{u}} {x y : X _⦋0⦌}
    (i : B ⟶ C)
    (f : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y))) :
    intervalFamilyTranspose (i ≫ f) = (A ◁ i) ≫ intervalFamilyTranspose f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective x y
  rw [intervalFamilyTranspose_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    intervalFamilyTranspose_uncurry, intervalTransposeUncurry_precomp]

/-- 概要：区間と A の交換は時間零の制限と整合する。
方針：三つの座標を次数ごとに比較する。
規約：時間は最後の Δ[1] 因子。
使われ方：転置したホモトピーの始点の計算。 -/
lemma intervalParameterSwap_time_zero (A : SSet.{u}) :
    (Δ[1] ◁ (SSet.ι₀ : A ⟶ A ⊗ Δ[1])) ≫ intervalParameterSwap A Δ[1] =
      (β_ (Δ[1] : SSet.{u}) A).hom ≫ (A ◁ (SSet.ι₀ : Δ[1] ⟶ Δ[1] ⊗ Δ[1])) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 概要：区間と A の交換は時間一の制限と整合する。
方針：三つの座標を次数ごとに比較する。
規約：時間は最後の Δ[1] 因子。
使われ方：転置したホモトピーの終点の計算。 -/
lemma intervalParameterSwap_time_one (A : SSet.{u}) :
    (Δ[1] ◁ (SSet.ι₁ : A ⟶ A ⊗ Δ[1])) ≫ intervalParameterSwap A Δ[1] =
      (β_ (Δ[1] : SSet.{u}) A).hom ≫ (A ◁ (SSet.ι₁ : Δ[1] ⟶ Δ[1] ⊗ Δ[1])) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
