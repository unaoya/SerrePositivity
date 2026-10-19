module
public import SerrePositivity.InfinityCategories.Derived.ChainMapHomotopyReflection
public import SerrePositivity.InfinityCategories.Derived.SemifreeCofiberZeroTriangle

/-! # 標準 cofiber 列の二つの射

概要：標準 cofiber の下辺と右辺は、元の鎖写像と cone への包含を表す。
方針：包含後の四角形の辺を計算し、h の類を忠実性で反映する。
規約：端点表示の等号も保持する。使われ方：D7 の三角形の像の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial ZeroObject
variable {S : Type u} [CommRing S] {X Y : Semifree S}

/-- 標準 cofiber 列の第一射は元の鎖写像の類。 -/
lemma semifreeCofiberZeroTriangle_f_arrow (f : X.val ⟶ Y.val) :
    Arrow.mk (semifreeCofiberZeroTriangle f).hoShortComplex.f =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (derivedChainMapEdge (x := Simplex.vertex X) (y := Simplex.vertex Y) f)) := by
  apply derived_homMk_arrow_eq_of_inclusion
  change derivedInfinityInclusion.app _ (squareBottomArrow
    (semifreeCofiberZeroTriangle f).square).edge = _
  rw [squareBottomArrow_edge, ← SSet.yonedaEquiv_comp, Category.assoc,
    semifreeCofiberZeroTriangle_inclusion, cofiberComplexSquareData_square,
    standardCofiberSquare_bottom, Equiv.apply_symm_apply]

/-- 標準 cofiber 列の第二射は cone への包含の類。 -/
lemma semifreeCofiberZeroTriangle_g_arrow (f : X.val ⟶ Y.val) :
    Arrow.mk (semifreeCofiberZeroTriangle f).hoShortComplex.g =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (derivedChainMapEdge (x := Simplex.vertex Y)
          (y := Simplex.vertex (semifreeCofiberZeroObject f))
          (pushoutInclusionB f (0 : X.val ⟶ 0)))) := by
  apply derived_homMk_arrow_eq_of_inclusion
  change derivedInfinityInclusion.app _ (squareRightArrow
    (semifreeCofiberZeroTriangle f).square).edge = _
  rw [squareRightArrow_edge, ← SSet.yonedaEquiv_comp, Category.assoc,
    semifreeCofiberZeroTriangle_inclusion, cofiberComplexSquareData_square,
    standardCofiberSquare_right, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.InfinityCategories
