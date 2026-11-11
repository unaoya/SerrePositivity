module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorFamilyPrism

/-!
概要：関手単体集合の三角形と恒等辺の prism 表示の計算。
方針：Yoneda 射の辺への制限とパラメーター付き評価の自然性を使う。
規約：単体集合の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、unstraightening の恒等・合成則を関手空間に適用する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：関手空間の合成三角形の prism の最初の辺は最初の変換の prism。
方針：パラメーター制限と三角形の二番目の面の計算を使う。
規約：欠ける頂点は 2。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、変換の合成三角形の初辺。 -/
lemma functorCompStructPrism_two {B X : SSet.{u}} {F G J : B ⟶ X}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)}
    {g : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)} (σ : SSet.Truncated.Edge.CompStruct e f g) :
    (stdSimplex.δ (2 : Fin 3) ▷ B) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism (SSet.yonedaEquiv.symm σ.simplex) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism e := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism_restrict]
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism (SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm σ)

/-- 概要：関手空間の合成三角形の prism の後半の辺は後半の変換の prism。
方針：パラメーター制限と三角形の零番目の面の計算を使う。
規約：欠ける頂点は 0。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、変換の合成三角形の後辺。 -/
lemma functorCompStructPrism_zero {B X : SSet.{u}} {F G J : B ⟶ X}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)}
    {g : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)} (σ : SSet.Truncated.Edge.CompStruct e f g) :
    (stdSimplex.δ (0 : Fin 3) ▷ B) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism (SSet.yonedaEquiv.symm σ.simplex) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism f := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism_restrict]
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism (SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm σ)

/-- 概要：関手空間の合成三角形の prism の長辺は合成後の変換の prism。
方針：パラメーター制限と三角形の一番目の面の計算を使う。
規約：欠ける頂点は 1。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、選択した長辺と二辺の合成の比較。 -/
lemma functorCompStructPrism_one {B X : SSet.{u}} {F G J : B ⟶ X}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)}
    {g : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex J)} (σ : SSet.Truncated.Edge.CompStruct e f g) :
    (stdSimplex.δ (1 : Fin 3) ▷ B) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism (SSet.yonedaEquiv.symm σ.simplex) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism g := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism_restrict]
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism (SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm σ)

/-- 概要：関手空間の恒等辺の prism は区間に関して定値な関手の族。
方針：各次数で評価の第二成分を計算する。
規約：任意の単体集合間の関手を扱う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、unstraightening の恒等変換との接続。 -/
lemma functorEdgePrism_id {B X : SSet.{u}} (F : B ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism (F := F) (G := F)
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom B).obj X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) = snd (Δ[1] : SSet.{u}) B ≫ F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨t, b⟩
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
