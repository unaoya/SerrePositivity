module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronNextComparison

/-! # 八面体の二つの三角形比較と最後の列

概要：二つの三角形の射の成分を、三つの元の列と最後の列の射へ同時に照合する。
方針：関手圏の評価との一致、共有辺の厳密な式、端点を含む Arrow の等号を使う。
規約：一般の前三角圏での八面体への組み立ては別途必要。使われ方：TR4 の四可換式の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Pretriangulated MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：最初の比較の中間成分は二つ目の元の列の第一射。
方針：両者を最初の長方形の右面の下辺に照合する。
規約：端点の表示を Arrow に保持。使われ方：八面体の第一可換式で使う中間射。 -/
lemma CofiberOctahedronDiagram.firstTriangle_middle_arrow {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X} (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    Arrow.mk (d.first.triangleMorphism ht).hom₂ =
      Arrow.mk d.second.outerZeroTriangle.hoShortComplex.f := by
  apply (d.first.triangleMorphism_middle_arrow ht).trans
  apply Eq.symm
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge]
  exact congrArg SSet.yonedaEquiv d.next_firstEdge

/-- 概要：最後の列の第一射は最初の三角形比較の第三成分。
方針：両者を最初の長方形の右面の上辺に照合する。
規約：cofiber 頂点の表示を Arrow に保持。使われ方：最後の三角形の第一射 m₁。 -/
lemma CofiberOctahedronDiagram.last_first_arrow {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X} (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    Arrow.mk d.second.rightZeroTriangle.hoShortComplex.f =
      Arrow.mk (d.first.triangleMorphism ht).hom₃ := by
  apply Eq.trans _ (d.first.triangleMorphism_target_arrow ht).symm
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge]
  exact congrArg SSet.yonedaEquiv d.last_firstEdge

/-- 概要：第二の三角形比較の第一成分は元の列の第一射。
方針：三角形の射の成分を図式の評価に戻し、合成比較の始点を使う。
規約：端点の表示を Arrow に保持。使われ方：八面体の第四可換式の始点条件。 -/
lemma CofiberOctahedronDiagram.nextTriangle_source_arrow {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    Arrow.mk d.nextTriangleMorphism.hom₁ = Arrow.mk t.hoShortComplex.f := by
  change Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangleHoMap _ _ _ _ d.nextComparisonHom).hom₁ = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangleHoMap_hom₁]
  exact d.nextComparison_source_arrow

/-- 概要：第二の三角形比較の中間成分は恒等射。
方針：三角形の射の成分を図式の評価に戻し、合成比較の固定条件を使う。
規約：二つ目の射の終域の表示を許す。使われ方：八面体の第三可換式の中間条件。 -/
lemma CofiberOctahedronDiagram.nextTriangle_middle_arrow {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    Arrow.mk d.nextTriangleMorphism.hom₂ =
      Arrow.mk (𝟙 d.first.outerZeroTriangle.hoShortComplex.X₂) := by
  change Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangleHoMap _ _ _ _ d.nextComparisonHom).hom₂ = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangleHoMap_hom₂]
  exact d.nextComparison_middle_arrow

/-- 概要：最後の列の第二射は第二の三角形比較の第三成分。
方針：三角形の射の成分を図式の評価へ戻し、右面の上辺を使う。
規約：cofiber 頂点の表示を Arrow に保持。使われ方：最後の三角形の第二射 m₃。 -/
lemma CofiberOctahedronDiagram.last_second_arrow {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    Arrow.mk d.second.rightZeroTriangle.hoShortComplex.g =
      Arrow.mk d.nextTriangleMorphism.hom₃ := by
  change _ = Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangleHoMap _ _ _ _ d.nextComparisonHom).hom₃
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangleHoMap_hom₃]
  exact d.nextComparison_target_arrow.symm

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
