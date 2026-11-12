module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.SquareClass

/-!
概要：写像空間の族のホモトピーを定値関手間の辺の正方形に展開する。
方針：射・時間・パラメータの順序を交換して curry し、四辺を計算する。
規約：四辺の計算には quasicategory 性は不要。
使われ方：族の表示のホモトピー不変性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：パラメータ・射・時間を射・パラメータ・時間へ並べ替える。
方針：結合子と最初の二座標の対称性を使う。
規約：最後の座標がホモトピーの時間。
使われ方：正方形を h Fun の射として表示する。 -/
def intervalFamilySquareReorder (A : SSet.{u}) :
    A ⊗ ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⟶ (Δ[1] : SSet.{u}) ⊗ (A ⊗ Δ[1]) :=
  (α_ A Δ[1] Δ[1]).inv ≫ ((β_ A (Δ[1] : SSet.{u})).hom ▷ Δ[1]) ≫
    (α_ Δ[1] A Δ[1]).hom

/-- 概要：写像空間の族のホモトピーが定める関手単体集合の正方形。
方針：区間の族を展開し、座標を並べ替えて curry する。
規約：第一座標が射、第二座標が時間。
使われ方：四辺の合成関係から h Fun の射の等式を得る。 -/
noncomputable def intervalFamilySquare {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y} (H : SSet.Homotopy f g) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom A).obj X :=
  curry (intervalFamilySquareReorder A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry H.h)

/-- 概要：正方形の時間零の辺は最初の族の区間の curry。
方針：座標の並べ替えと H の端点条件を使う。
規約：辺の代表を変えない。
使われ方：正方形の下辺の計算。 -/
lemma intervalFamilySquare_zero {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y} (H : SSet.Homotopy f g) :
    SSet.ι₀ ≫ intervalFamilySquare H = curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  simp only [intervalFamilySquare, uncurry_curry]
  have hc : A ◁ (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
      intervalFamilySquareReorder A =
        (β_ A (Δ[1] : SSet.{u})).hom ≫ (Δ[1] : SSet.{u}) ◁ SSet.ι₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  rw [← Category.assoc, hc, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, H.h₀]
  rfl

/-- 概要：正方形の時間一の辺は最後の族の区間の curry。
方針：座標の並べ替えと H の端点条件を使う。
規約：辺の代表を変えない。
使われ方：正方形の上辺の計算。 -/
lemma intervalFamilySquare_one {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y} (H : SSet.Homotopy f g) :
    SSet.ι₁ ≫ intervalFamilySquare H = curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy g).h := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  simp only [intervalFamilySquare, uncurry_curry]
  have hc : A ◁ (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
      intervalFamilySquareReorder A =
        (β_ A (Δ[1] : SSet.{u})).hom ≫ (Δ[1] : SSet.{u}) ◁ SSet.ι₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  rw [← Category.assoc, hc, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, H.h₁]
  rfl

/-- 概要：正方形の始点側は全時間で定値関手 x。
方針：座標を並べ替えて固定端点の公式を使う。
規約：時間の辺は退化する。
使われ方：正方形の左辺の計算。 -/
lemma intervalFamilySquare_source {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y} (H : SSet.Homotopy f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ intervalFamilySquare H =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X)) := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  simp only [intervalFamilySquare, uncurry_curry]
  have hc : A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ intervalFamilySquareReorder A =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (A ⊗ (Δ[1] : SSet.{u})) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  rw [← Category.assoc, hc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex, SSet.comp_const]

/-- 概要：正方形の終点側は全時間で定値関手 y。
方針：座標を並べ替えて固定端点の公式を使う。
規約：時間の辺は退化する。
使われ方：正方形の右辺の計算。 -/
lemma intervalFamilySquare_target {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y} (H : SSet.Homotopy f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ intervalFamilySquare H =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y : A ⟶ X)) := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  simp only [intervalFamilySquare, uncurry_curry]
  have hc : A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ intervalFamilySquareReorder A =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (A ⊗ (Δ[1] : SSet.{u})) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  rw [← Category.assoc, hc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_one, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex, SSet.comp_const]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
