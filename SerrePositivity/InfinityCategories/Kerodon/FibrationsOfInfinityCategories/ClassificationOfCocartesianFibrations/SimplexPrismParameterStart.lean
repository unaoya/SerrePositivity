module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexPrismFirstVertex

/-!
概要：追加パラメーターを持つ単体の prism の最初の値の計算。
方針：最初の頂点の包含の分解と、テンソルおよび射影の自然性を使う。
規約：追加パラメーターに対して底の族は変化してよい。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、始点を固定した相対的な高次の持ち上げ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：最初の値が追加パラメーターに関して定値な単体の族を引き戻したときの始点を計算する。
方針：頂点包含の自然性と第一射影の自然性でパラメーターを忘れる。
規約：p、F、T は任意の単体集合の射。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、pointed space の初期図式と底の族の可換性。 -/
lemma simplexPrism_parameterizedStart {A B L X : SSet.{u}}
    (p : A ⟶ B) (F : B ⟶ X) (n : ℕ)
    (T : ((Δ[n] : SSet.{u}) ⊗ B) ⊗ L ⟶ X)
    (h₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n 0 B ▷ L) ≫ T = fst B L ≫ F) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n ▷ A) ▷ L) ≫ ((Δ[n] ◁ p) ▷ L)) ≫ T =
      fst (Δ[0] ⊗ A) L ≫ snd (Δ[0] : SSet.{u}) A ≫ p ≫ F := by
  rw [← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex_naturality]
  simp only [comp_whiskerRight, Category.assoc, h₀, whiskerRight_fst_assoc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
