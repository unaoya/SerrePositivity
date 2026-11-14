module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.FirstTriangleIndex

/-! # 最初の右頂点との join の三角形

概要：辺と右因子の最初の点の join は標準セルの最初の三頂点に対応する。
方針：join の左右の包含で比較し、有限頂点写像の値を計算する。
規約：固定の二頂点を左に置く。使われ方：D7 の余錐の左右三角形の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite
open scoped _root_.Simplicial

/-- 概要：辺と最初の右頂点の join は最初の三頂点の三角形。
方針：左右の包含で標準 join 同型の値を計算する。
規約：右因子の頂点は零番。使われ方：余錐の固定三角形の回収。 -/
lemma cofiberJoinStdSimplexIso_first_triangle (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[1] : SSet.{u}))
        (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ SSet.stdSimplex.map
        (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_hom_to_stdSimplex_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberJoinStdSimplexIso_inl, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inl]
    rw [← CategoryTheory.Functor.map_comp]
    apply congrArg SSet.stdSimplex.map
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    rfl
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberJoinStdSimplexIso_inr, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inr]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    apply congrArg SSet.stdSimplex.map
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    have hi : i = 0 := Fin.eq_zero (show Fin 1 from i)
    subst i
    rfl

/-- 概要：左の余錐三角形を最初の可変点へ送るとセルの最初の三角形になる。
方針：最初の三角形の join 公式を逆向きに使い、joinMap の合成則を計算する。
規約：固定二点は保つ。使われ方：左の指定余錐の回収。 -/
lemma spanJoinLeft_first_triangle (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{u}))
        (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)) =
      SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft n := by
  have hi : SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).inv =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[1])
          (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)) := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [cofiberJoinStdSimplexIso_first_triangle, Iso.inv_hom_id_assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft, ← Category.assoc]
  rw [hi]
  simp only [Category.assoc]
  congr 1
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
  simp only [Category.id_comp, Category.comp_id]

/-- 概要：右の余錐三角形を最初の可変点へ送るとセルの最初の三角形になる。
方針：最初の三角形の join 公式を逆向きに使い、joinMap の合成則を計算する。
規約：固定二点は保つ。使われ方：右の指定余錐の回収。 -/
lemma spanJoinRight_first_triangle (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{u}))
        (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)) =
      SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight n := by
  have hi : SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.firstTriangleOrderHom n)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).inv =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[1])
          (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)) := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberJoinStdSimplexIso 1 n (n + 2) (by omega)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [cofiberJoinStdSimplexIso_first_triangle, Iso.inv_hom_id_assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight, ← Category.assoc]
  rw [hi]
  simp only [Category.assoc]
  congr 1
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
  simp only [Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
