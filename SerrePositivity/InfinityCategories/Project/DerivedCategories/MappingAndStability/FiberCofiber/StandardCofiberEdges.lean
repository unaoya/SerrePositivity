module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.ChainMapHomotopyReflection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.SemifreeCofiberZeroTriangle

/-! # 標準 cofiber 列の二つの射

概要：標準 cofiber の下辺と右辺は、元の鎖写像と cone への包含を表す。
方針：包含後の四角形の辺を計算し、h の類を忠実性で反映する。
規約：端点表示の等号も保持する。使われ方：D7 の三角形の像の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial ZeroObject
variable {S : Type u} [CommRing S] {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}

/-- 標準 cofiber 列の第一射は元の鎖写像の類。 -/
lemma semifreeCofiberZeroTriangle_f_arrow (f : X.val ⟶ Y.val) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f).hoShortComplex.f =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) f)) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_homMk_arrow_eq_of_inclusion
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion.app _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f).square).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge, ← SSet.yonedaEquiv_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_inclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData_square,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare_bottom, Equiv.apply_symm_apply]

/-- 標準 cofiber 列の第二射は cone への包含の類。 -/
lemma semifreeCofiberZeroTriangle_g_arrow (f : X.val ⟶ Y.val) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f).hoShortComplex.g =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)
          (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f))
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB f (0 : X.val ⟶ 0)))) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_homMk_arrow_eq_of_inclusion
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion.app _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f).square).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow_edge, ← SSet.yonedaEquiv_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_inclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData_square,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare_right, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
