module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoin
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram

/-!
概要：動く定値図式への自然変換から太い余錐を厳密に回収する。
方針：K 変数を uncurry し、円柱と両端を fat join の二段の押し出しで貼る。
規約：指定された図式・頂点・自然変換を変更しない。
使われ方：太い coslice と対角 comma の族の比較の逆構成。

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

/-- 概要：K・時間・パラメータを K・パラメータ・時間に戻す。
方針：結合子と最後の二因子の交換を使う。
規約：時間の向きは保つ。使われ方：自然変換の円柱の uncurry。 -/
def diagonalCoconeUnreorder (K A : SSet.{u}) :
    (K ⊗ (Δ[1] : SSet.{u})) ⊗ A ⟶ K ⊗ (A ⊗ (Δ[1] : SSet.{u})) :=
  (α_ K (Δ[1] : SSet.{u}) A).hom ≫ (K ◁ (β_ (Δ[1] : SSet.{u}) A).hom)

/-- 概要：逆の並べ替えは円柱の零端を保持する。
方針：直積の座標で計算する。
規約：時間の向きを保持する。使われ方：貼り合わせの始点条件。 -/
lemma diagonalCoconeUnreorder_zero (K A : SSet.{u}) :
    (SSet.ι₀ (X := K) ▷ A) ≫ diagonalCoconeUnreorder K A = (K ◁ SSet.ι₀) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 概要：逆の並べ替えは円柱の一端を保持する。
方針：直積の座標で計算する。
規約：時間の向きを保持する。使われ方：貼り合わせの終点条件。 -/
lemma diagonalCoconeUnreorder_one (K A : SSet.{u}) :
    (SSet.ι₁ (X := K) ▷ A) ≫ diagonalCoconeUnreorder K A = (K ◁ SSet.ι₁) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 概要：定値図式への指定自然変換から太い余錐を構成する。
方針：自然変換を K 変数について評価し、元の図式・頂点と貼り合わせる。
規約：自然変換のホモトピー類だけでなく実際の射を保つ。
使われ方：対角 comma の族から太い coslice の族への逆写像。 -/
def fatCoconeFromHomotopy {A K C : SSet.{u}} (p : K ⟶ C) (b : A ⟶ C)
    (H : SSet.Homotopy (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin K A ⟶ C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinDesc p b (diagonalCoconeUnreorder K A ≫ uncurry H.h)
    (by
      rw [← Category.assoc, diagonalCoconeUnreorder_zero,
        ← uncurry_natural_left, H.h₀, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex])
    (by
      rw [← Category.assoc, diagonalCoconeUnreorder_one,
        ← uncurry_natural_left, H.h₁, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.uncurry_comp_constantDiagram])

/-- 概要：回収した太い余錐は元の左図式を厳密に保持する。
方針：fat join の貼り合わせの左端の式。
規約：p は任意。使われ方：太い coslice の固定条件。 -/
lemma fatCoconeFromHomotopy_fixed {A K C : SSet.{u}} (p : K ⟶ C) (b : A ⟶ C)
    (H : SSet.Homotopy (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K A ≫ fatCoconeFromHomotopy p b H = p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_desc _ _ _ _ _

/-- 概要：回収した太い余錐の右端は元の頂点族。
方針：fat join の貼り合わせの右端の式。
規約：b は非定値でよい。使われ方：対角 comma の標的を保つ比較。 -/
lemma fatCoconeFromHomotopy_apex {A K C : SSet.{u}} (p : K ⟶ C) (b : A ⟶ C)
    (H : SSet.Homotopy (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K A ≫ fatCoconeFromHomotopy p b H = b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_desc _ _ _ _ _

/-- 概要：回収した太い余錐の円柱は元の自然変換の評価。
方針：二段の押し出しの円柱上の計算。
規約：時間の並べ替えを明示する。使われ方：往復則の計算。 -/
lemma fatCoconeFromHomotopy_cylinder {A K C : SSet.{u}} (p : K ⟶ C) (b : A ⟶ C)
    (H : SSet.Homotopy (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder K A ≫ fatCoconeFromHomotopy p b H =
      diagonalCoconeUnreorder K A ≫ uncurry H.h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_desc _ _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
