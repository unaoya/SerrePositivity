module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.SquareThreeEdges

/-!
概要：正方形の全境界を三辺の和と右辺の像の和として扱う。
方針：和の各単体を三辺部分図式または右辺へ戻して射の等式を検査する。
規約：全境界への包含は単射。正方形の内部を含めない。
使われ方：B1 の二つの全体輸送の境界 path を照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：正方形の四辺の和。
方針：固定した三辺の和に右辺の像を加える。
規約：正方形への部分単体集合として定義する。
使われ方：境界固定の図式ホモトピーの部分図式。 -/
noncomputable def squareBoundary : ((Δ[1] : SSet.{u}) ⊗ Δ[1]).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges ⊔ Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}))

/-- 概要：三辺と右辺で一致する図式は全境界でも一致する。
方針：各境界単体が三辺部分図式か右辺の像に含まれることを使う。
規約：値域に quasicategory 性は不要。
使われ方：輸送の一意性に必要な境界 path 全体の等式。 -/
lemma squareBoundary_restriction_eq {Z : SSet.{u}}
    (f g : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Z)
    (h₃ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι ≫ f = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.ι ≫ g)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ g) :
    squareBoundary.ι ≫ f = squareBoundary.ι ≫ g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨q, hq⟩
  change f.app n q = g.app n q
  change q ∈ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdges.obj n ∨
    (∃ e, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u})).app n e = q) at hq
  rcases hq with hq | ⟨e, rfl⟩
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app h₃ n) ⟨q, hq⟩
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app hr n) e

/-- 概要：全境界で一致する図式は、その中の任意の射でも一致する。
方針：部分単体集合への持ち上げで前合成する。
規約：射の像が全境界に含まれることを明示する。
使われ方：全境界固定の条件から各辺の固定を取り出す。 -/
lemma squareBoundary_restriction_edge {K Z : SSet.{u}}
    {f g : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Z}
    (h : squareBoundary.ι ≫ f = squareBoundary.ι ≫ g)
    (e : K ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[1]) (he : Subcomplex.range e ≤ squareBoundary) :
    e ≫ f = e ≫ g := by
  have hh := congrArg (fun k ↦ Subcomplex.lift e he ≫ k) h
  simpa only [← Category.assoc, Subcomplex.lift_ι] using hh

/-- 概要：下辺の像は全境界に含まれる。
方針：三回の和への包含を合成する。
規約：像の包含として述べる。
使われ方：転置した正方形の下辺の固定。 -/
lemma squareBoundary_range_bottom_le :
    Subcomplex.range (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≤ squareBoundary :=
  le_trans (le_trans le_sup_left le_sup_left) le_sup_left

/-- 概要：左辺の像は全境界に含まれる。
方針：三回の和への包含を合成する。
規約：像の包含として述べる。
使われ方：転置した正方形の左辺の固定。 -/
lemma squareBoundary_range_left_le :
    Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u})) ≤ squareBoundary :=
  le_trans (le_trans le_sup_right le_sup_left) le_sup_left

/-- 概要：上辺の像は全境界に含まれる。
方針：二回の和への包含を合成する。
規約：像の包含として述べる。
使われ方：転置した正方形の上辺の固定。 -/
lemma squareBoundary_range_top_le :
    Subcomplex.range (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≤ squareBoundary :=
  le_trans le_sup_right le_sup_left

/-- 概要：右辺の像は全境界に含まれる。
方針：全境界を定義する和の右側の包含を使う。
規約：像の包含として述べる。
使われ方：転置した正方形の右辺の固定。 -/
lemma squareBoundary_range_right_le :
    Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u})) ≤ squareBoundary := le_sup_right

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
