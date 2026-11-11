module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LastTriangleIndex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanJoinCells

/-! # 最後の左頂点との join の三角形

概要：左因子の最後の頂点と辺の join は標準セルの最後の三頂点に対応する。
方針：join 同型を左右の包含で比較し、有限順序写像の値を計算する。
規約：HTT §1.2.8・§1.2.13。使われ方：境界の最後の錐の三角形を左右セルで同定する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite
open scoped _root_.Simplicial

/-- 概要：最後の左頂点との辺の join は最後の三頂点の標準三角形。
方針：左包含では最後の頂点、右包含では最後の二頂点の番号を比較する。
規約：HTT §1.2.8・§1.2.13。使われ方：最後の三角形と join の標準表示の可換性。 -/
lemma joinStdSimplexIso_last_triangle (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)))
        (𝟙 (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom ≫ SSet.stdSimplex.map
        (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom n)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_hom_to_stdSimplex_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inl,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inl]
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg SSet.stdSimplex.map
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    have hi : i = 0 := Fin.eq_zero (show Fin 1 from i)
    subst i
    rfl
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inr,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inr]
    rw [← Functor.map_comp]
    apply congrArg SSet.stdSimplex.map
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    apply Fin.ext
    change n + 1 + i.val = n + (1 + i.val)
    omega

/-- 概要：左の錐三角形を最後の左頂点へ送ると、左セルの最後の三角形になる。
方針：最後の頂点との join の同型を逆向きに使い、joinMap の合成則を計算する。
規約：HTT §1.2.13。使われ方：B,D 側の標準錐の三角形の回収。 -/
lemma cospanJoinLeft_last_triangle (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleLeft.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap
        (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)))
        (𝟙 (SSet.horn 2 2 : SSet.{u})) =
      SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom n)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinLeft n := by
  have hi : SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom n)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).inv = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap
        (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n))) (𝟙 Δ[1]) := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [joinStdSimplexIso_last_triangle, Iso.inv_hom_id_assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleLeft, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinLeft, ← Category.assoc]
  rw [hi]
  simp only [Category.assoc]
  congr 1
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
  simp only [Category.id_comp, Category.comp_id]

/-- 概要：右の錐三角形を最後の左頂点へ送ると、右セルの最後の三角形になる。
方針：最後の頂点との join の同型を逆向きに使い、joinMap の合成則を計算する。
規約：HTT §1.2.13。使われ方：C,D 側の標準錐の三角形の回収。 -/
lemma cospanJoinRight_last_triangle (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleRight.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap
        (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)))
        (𝟙 (SSet.horn 2 2 : SSet.{u})) =
      SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom n)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinRight n := by
  have hi : SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastTriangleOrderHom n)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).inv = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap
        (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n))) (𝟙 Δ[1]) := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [joinStdSimplexIso_last_triangle, Iso.inv_hom_id_assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleRight, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanJoinRight, ← Category.assoc]
  rw [hi]
  simp only [Category.assoc]
  congr 1
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
  simp only [Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
