module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomotopyTriangleFillingCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FunctorSquareRawHomotopy
/-! # 指定三辺の充填を同じ全 path 正方形へ移す

概要：指定境界を満たす二単体そのものから、三辺を保つ全 path の実正方形を得る。
方針：境界の三制限を合成三角形へ戻し、F1B の公開正方形補完を uncurry する。
規約：充填の二単体・指定三辺・全時間を保持する。
使われ方：④で構成した指定境界を⑤の path 引き戻し比較へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
variable {K Z : SSet.{u}} {a b c : K ⟶ Z}
  {l : SSet.Homotopy a b} {r : SSet.Homotopy b c} {d : SSet.Homotopy a c}
  (T : (Δ[2] : SSet.{u}) ⟶ (ihom K).obj Z)
  (hT : (boundary 2).ι ≫ T = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary l r d)

def dgGluingFunctorTriangleOfBoundaryFilling : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d where
  diagram := T
  face_zero := by
    have h := congrArg (fun q => boundary.ι (0 : Fin 3) ≫ q) hT
    simpa only [← Category.assoc, boundary.ι_ι, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary_zero] using h
  face_one := by
    have h := congrArg (fun q => boundary.ι (1 : Fin 3) ≫ q) hT
    simpa only [← Category.assoc, boundary.ι_ι, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary_one] using h
  face_two := by
    have h := congrArg (fun q => boundary.ι (2 : Fin 3) ≫ q) hT
    simpa only [← Category.assoc, boundary.ι_ι, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary_two] using h

def dgGluingBoundaryFillingPathSquare : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl a).h r.h :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorSquareRawHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle (dgGluingFunctorTriangleOfBoundaryFilling T hT))

lemma dgGluingBoundaryFillingPathSquare_left :
    ((ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
      (dgGluingBoundaryFillingPathSquare T hT).h = l.h :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorSquareRawMap_left _

lemma dgGluingBoundaryFillingPathSquare_right :
    ((ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
      (dgGluingBoundaryFillingPathSquare T hT).h = d.h :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorSquareRawMap_right _
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
