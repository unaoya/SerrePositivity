module
public import SerrePositivity.KST.SConstruction.SpecifiedTwoTrianglePrism
public import SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorTriangleSquare

/-!
概要：指定四境界比較から、元の上下二単体を保つ比較 prism をそれぞれ構成する。
方針：上面は左・上辺、下面は下・右辺を同じ中間頂点経路で貼る。
規約：元二単体と元四側面を保持。共有対角の一致は別の接合条件。
使われ方：恒等実右面の上下二胞体の全比較と残る共有対角の整列。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet InfinityCategories LocalizingInvariants
open scoped Simplicial
variable {X : SSet.{u}} [Quasicategory X]
  {f g : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
  (H : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare f) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare g))

/-- 概要：元上面の左辺・下面の下辺の全比較を元二単体の前辺に表示する。
方針：標準二三角形の元前辺の式を使う。
規約：全比較写像を保持。使われ方：元三角形比較の第一側面。 -/
def squareFrameTriangleFirst (j : Fin 2) : SSet.Homotopy
    (stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ f)
    (stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ g) where
  h := if j = 0 then H.left.h else H.bottom.h
  h₀ := by
    fin_cases j
    · change SSet.ι₀ ≫ H.left.h = _
      exact H.left.h₀.trans ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] => k ≫ f)
          _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_upper_left)).symm
    · change SSet.ι₀ ≫ H.bottom.h = _
      exact H.bottom.h₀.trans ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] => k ≫ f)
          _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_lower_bottom)).symm
  h₁ := by
    fin_cases j
    · change SSet.ι₁ ≫ H.left.h = _
      exact H.left.h₁.trans ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] => k ≫ g)
          _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_upper_left)).symm
    · change SSet.ι₁ ≫ H.bottom.h = _
      exact H.bottom.h₁.trans ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] => k ≫ g)
          _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_lower_bottom)).symm
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：元上面の上辺・下面の右辺の全比較を元二単体の後辺に表示する。
方針：標準二三角形の元後辺の式を使う。
規約：全比較写像を保持。使われ方：元三角形比較の第二側面。 -/
def squareFrameTriangleLast (j : Fin 2) : SSet.Homotopy
    (stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ f)
    (stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ g) where
  h := if j = 0 then H.top.h else H.right.h
  h₀ := by
    fin_cases j
    · change SSet.ι₀ ≫ H.top.h = _
      exact H.top.h₀.trans ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] => k ≫ f)
          _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_upper_top)).symm
    · change SSet.ι₀ ≫ H.right.h = _
      exact H.right.h₀.trans ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] => k ≫ f)
          _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_lower_right)).symm
  h₁ := by
    fin_cases j
    · change SSet.ι₁ ≫ H.top.h = _
      exact H.top.h₁.trans ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] => k ≫ g)
          _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_upper_top)).symm
    · change SSet.ι₁ ≫ H.right.h = _
      exact H.right.h₁.trans ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] => k ≫ g)
          _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_lower_right)).symm
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：同じ三角形二側面の中間頂点経路は元四境界比較から厳密に一致する。
方針：上面では元左上、下面では元右下の共有経路式を使う。
規約：頂点経路を選び直さない。使われ方：内ホーンへの二側面の接合。 -/
lemma squareFrameTriangle_middle (j : Fin 2) :
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ (squareFrameTriangleFirst H j).h =
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ (squareFrameTriangleLast H j).h := by
  fin_cases j
  · exact H.upper_left.symm
  · exact H.lower_right

/-- 概要：元上面・下面それぞれの二単体を元二短辺比較で結ぶ全ホモトピー。
方針：共有頂点経路で貼った内ホーンを両端固定で延長する。
規約：元二単体・元四側面を保持。使われ方：共有対角を整列する二つの実比較。 -/
def squareFrameTriangleHomotopy (j : Fin 2) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ g) :=
  specifiedTwoTriangleHomotopy _ _ (squareFrameTriangleFirst H j)
    (squareFrameTriangleLast H j) (squareFrameTriangle_middle H j)

/-- 概要：元上下比較の二短辺制限は指定した元四境界比較そのもの。
方針：両端固定 prism の元側面回収を使う。
規約：全単体の厳密等号。使われ方：全四角形を貼る際の元境界保持。 -/
lemma squareFrameTriangleHomotopy_faces (j : Fin 2) :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ (squareFrameTriangleHomotopy H j).h =
        (squareFrameTriangleFirst H j).h ∧
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ (squareFrameTriangleHomotopy H j).h =
        (squareFrameTriangleLast H j).h :=
  specifiedTwoTriangleHomotopy_faces _ _ (squareFrameTriangleFirst H j)
    (squareFrameTriangleLast H j) (squareFrameTriangle_middle H j)
end SerrePositivity.KST.SConstruction
