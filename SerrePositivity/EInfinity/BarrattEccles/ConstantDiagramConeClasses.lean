module

public import SerrePositivity.EInfinity.BarrattEccles.ConstantDiagramClasses
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointwiseConePoints
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.RealizationAugmentation
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConstantNaturality

/-!
# 通常の錐の始域 frame によるクラスの成分表示

概要：BM 命題 4.1・Hovey §5.4 の元の錐の類を同じ重み付き族で表示する。
方針：図式 frame の零次同型と各値の実現随伴の単体の式を使う。
規約：元の定値図式比較と元の代数射を保持する。
使われ方：右 frame の同じ錐の類との混合 Hom 内での照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

local instance : HasColimitsOfSize.{0, u} (operad A).Algebra :=
  hasColimitsOfSizeShrink.{0, u} _

/-- 概要：元の錐の類は定値図式比較の随伴像による錐の類（Hovey §5.4）。
方針：同じ図式 frame の零次比較と随伴で作った零単体を照合する。
規約：元の constantDiagramSourceClass を変更しない。
使われ方：混合 Hom 比較へ入力する元の錐の族。 -/
lemma constantDiagramSourceClass_eq_coneClass {Y : (operad A).Algebra}
    {F : K ⥤ (operad A).Algebra} (f : (Functor.const K).obj Y ⟶ F) :
    constantDiagramSourceClass A K f =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
        ((constantDiagramHomEquiv A K Y F) ((constantDiagramComparison A K).app Y ≫ f)) := by
  let := modelCategory A
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  rw [constantDiagramSourceClass, SSet.mapπ₀_mk, constantDiagramFrameComparison_zero]
  apply congrArg SSet.π₀.mk
  rw [Category.assoc]
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameHomIso_point K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    (q.obj.obj Y) ((constantDiagramComparison A K).app Y ≫ f)

/-- 概要：元の錐の随伴族は各成分で同じ augmentation の後合成（Hovey §5.4）。
方針：同じ実現比較の式を実現随伴の全単体の計算へ代入する。
規約：重みの単体には依存せず、元の frame の全次数を含む。
使われ方：右 frame の族と元の混合 Hom で厳密に一致することの証明。 -/
lemma constantDiagramHomEquiv_comparison_app {Y : (operad A).Algebra}
    {F : K ⥤ (operad A).Algebra} (f : (Functor.const K).obj Y ⟶ F)
    (k : K) (n : SimplexCategoryᵒᵖ) (x : ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K).obj k).obj n) :
    let := modelCategory A
    let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
    ((((constantDiagramHomEquiv A K Y F)
        ((constantDiagramComparison A K).app Y ≫ f)).app k).app n) x =
      (q.augmentation.app Y).app n.unop ≫ f.app k := by
  let := modelCategory A
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  let B := q.obj.obj Y
  let g := (((constantDiagramComparison A K).app Y).app k)
  change (((Realization.adjunction B).homEquiv _ _ (g ≫ f.app k)).app n) x = _
  have hg : g = (Realization.functor B).map ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K).app k) ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationPointIso B).hom ≫
        (q.augmentation.app Y).app (SimplexCategory.mk 0) :=
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseFrameComparison_app K (B := B) _ k
  have hp : (((Realization.adjunction B).homEquiv _ Y g).app n) x =
      (q.augmentation.app Y).app n.unop := by
    rw [hg]
    exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationAugmentation_homEquiv B (q.augmentation.app Y) _ _ n x
  have hn := congrArg (fun h => (h.app n) x)
    ((Realization.adjunction B).homEquiv_naturality_right g (f.app k))
  exact hn.trans (congrArg (fun h => h ≫ f.app k) hp)

end SerrePositivity.EInfinity.BarrattEccles
