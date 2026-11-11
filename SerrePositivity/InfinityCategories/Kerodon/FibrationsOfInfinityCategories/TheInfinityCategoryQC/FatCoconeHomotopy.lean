module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoin
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram

/-!
概要：太い余錐から対角関手への自然変換を、任意のパラメータで取り出す。
方針：太い join の円柱の K 変数を curry する。
規約：図式 p は固定し、余錐の頂点はパラメータ全体で動かす。
使われ方：対角関手の comma と太い coslice の比較。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：K・パラメータ・時間を、K・時間・パラメータへ並べ替える。
方針：最後の二因子の交換と結合子を使う。
規約：時間の向きは保持する。使われ方：太い余錐の円柱の curry。 -/
def diagonalCoconeReorder (K A : SSet.{u}) :
    K ⊗ (A ⊗ (Δ[1] : SSet.{u})) ⟶ (K ⊗ (Δ[1] : SSet.{u})) ⊗ A :=
  (K ◁ (β_ A (Δ[1] : SSet.{u})).hom) ≫ (α_ K (Δ[1] : SSet.{u}) A).inv

/-- 概要：並べ替えた零端は太い join の円柱の零端。
方針：直積の座標で計算する。
規約：時間の向きを保持する。使われ方：ホモトピーの始点。 -/
lemma diagonalCoconeReorder_zero (K A : SSet.{u}) :
    (K ◁ SSet.ι₀) ≫ diagonalCoconeReorder K A = (SSet.ι₀ (X := K) ▷ A) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 概要：並べ替えた一端は太い join の円柱の一端。
方針：直積の座標で計算する。
規約：時間の向きを保持する。使われ方：ホモトピーの終点。 -/
lemma diagonalCoconeReorder_one (K A : SSet.{u}) :
    (K ◁ SSet.ι₁) ≫ diagonalCoconeReorder K A = (SSet.ι₁ (X := K) ▷ A) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 概要：固定した左図式の太い余錐は、図式から動く定値図式への自然変換を与える。
方針：円柱の K 変数を curry し、両端の潰しの式を使う。
規約：元の円柱の射をそのまま保持する。使われ方：対角 comma の族の構成。 -/
def fatCoconeHomotopy {A K C : SSet.{u}} {p : K ⟶ C}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin K A ⟶ C) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K A ≫ F = p) :
    SSet.Homotopy (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K A ≫ F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K C) where
  h := curry (diagonalCoconeReorder K A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder K A ≫ F)
  h₀ := by
    change SSet.ι₀ ≫ curry _ = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
    rw [← Category.assoc (K ◁ SSet.ι₀), diagonalCoconeReorder_zero]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_zero, Category.assoc, hF]
  h₁ := by
    change SSet.ι₁ ≫ curry _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K A ≫ F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K C
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.uncurry_comp_constantDiagram]
    rw [← Category.assoc (K ◁ SSet.ι₁), diagonalCoconeReorder_one]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_one, Category.assoc]
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
