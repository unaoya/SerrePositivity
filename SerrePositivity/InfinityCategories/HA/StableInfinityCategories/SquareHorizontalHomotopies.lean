module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StdSimplexProductMap
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyEvaluationPath
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberComparisonComposition

/-! # 四角形の水平な変形

概要：四角形から右の列への変形と、左の列から四角形への変形を構成する。
方針：横座標を時間との最大値・最小値で動かす。
規約：縦座標は保存する。使われ方：S4 の接続射の後の零合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：辺を横方向に一定な四角形として表す。
方針：縦座標で射を引き戻す。規約：左右の列は同じ辺。
使われ方：四角形間の比較の中間図式。 -/
def squareColumnDiagram {X : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ X) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X := snd Δ[1] Δ[1] ≫ f

/-- 概要：横座標を時間との最大値で右へ動かす。
方針：有限順序集合の三因子の単調写像を使う。
規約：時間は最後の因子。使われ方：右の列への変形。 -/
def squareHorizontalMaxShape : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1] ⟶ Δ[1] ⊗ Δ[1] where
  app n := ↾fun p ↦ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexTripleProductMap {
    toFun q := max q.1.1 q.2
    monotone' := fun _ _ h ↦ max_le_max h.1.1 h.2 }).app n p, p.1.2)
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · apply stdSimplex.ext
      intro j
      rfl
    · rfl

/-- 概要：横座標を時間との最小値で左から動かす。
方針：有限順序集合の三因子の単調写像を使う。
規約：時間は最後の因子。使われ方：左の列からの変形。 -/
def squareHorizontalMinShape : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1] ⟶ Δ[1] ⊗ Δ[1] where
  app n := ↾fun p ↦ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexTripleProductMap {
    toFun q := min q.1.1 q.2
    monotone' := fun _ _ h ↦ min_le_min h.1.1 h.2 }).app n p, p.1.2)
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · apply stdSimplex.ext
      intro j
      rfl
    · rfl

/-- 概要：右へ動かす変形の始点は恒等射。
方針：max(x,0)=x を各頂点で計算する。規約：厳密な等式。
使われ方：右へのホモトピーの始点。 -/
lemma squareHorizontalMaxShape_zero : SSet.ι₀ ≫ squareHorizontalMaxShape.{u} = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro p
  apply Prod.ext
  · apply stdSimplex.ext
    intro j
    exact max_eq_left (Fin.zero_le (p.1 j))
  · rfl

/-- 概要：右へ動かす変形の終点は右の列を横に一定にした図式。
方針：max(x,1)=1 を各頂点で計算する。規約：厳密な等式。
使われ方：右へのホモトピーの終点。 -/
lemma squareHorizontalMaxShape_one : SSet.ι₁ ≫ squareHorizontalMaxShape.{u} =
    snd Δ[1] Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro p
  apply Prod.ext
  · apply stdSimplex.ext
    intro j
    exact max_eq_right (Fin.le_last (p.1 j))
  · rfl

/-- 概要：左から動かす変形の始点は左の列を横に一定にした図式。
方針：min(x,0)=0 を各頂点で計算する。規約：厳密な等式。
使われ方：左からのホモトピーの始点。 -/
lemma squareHorizontalMinShape_zero : SSet.ι₀ ≫ squareHorizontalMinShape.{u} =
    snd Δ[1] Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro p
  apply Prod.ext
  · apply stdSimplex.ext
    intro j
    exact min_eq_right (Fin.zero_le (p.1 j))
  · rfl

/-- 概要：左から動かす変形の終点は恒等射。
方針：min(x,1)=x を各頂点で計算する。規約：厳密な等式。
使われ方：左からのホモトピーの終点。 -/
lemma squareHorizontalMinShape_one : SSet.ι₁ ≫ squareHorizontalMinShape.{u} = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro p
  apply Prod.ext
  · apply stdSimplex.ext
    intro j
    exact min_eq_left (Fin.le_last (p.1 j))
  · rfl

/-- 概要：四角形から右の列を横に一定にした図式へのホモトピー。
方針：横座標の最大値による変形の後で四角形を評価する。
規約：値域の quasicategory 性は不要。使われ方：比較を零対象経由にする準備。 -/
def squareHorizontalRightHomotopy {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    SSet.Homotopy F (squareColumnDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F)) where
  h := squareHorizontalMaxShape ≫ F
  h₀ := by rw [← Category.assoc, squareHorizontalMaxShape_zero, Category.id_comp]; rfl
  h₁ := by rw [← Category.assoc, squareHorizontalMaxShape_one, Category.assoc]; rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：左の列を横に一定にした図式から四角形へのホモトピー。
方針：横座標の最小値による変形の後で四角形を評価する。
規約：値域の quasicategory 性は不要。使われ方：suspension への比較の最後の段階。 -/
def squareHorizontalLeftHomotopy {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    SSet.Homotopy (squareColumnDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ F)) F where
  h := squareHorizontalMinShape ≫ F
  h₀ := by rw [← Category.assoc, squareHorizontalMinShape_zero, Category.assoc]; rfl
  h₁ := by rw [← Category.assoc, squareHorizontalMinShape_one, Category.id_comp]; rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
