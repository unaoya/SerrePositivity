module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.VertexFiberModels

/-!
概要：全空間と底の可換正方形が頂点 fiber に誘導する実際の射と同値性。
方針：二つの厳密な fiber 模型の同型で既存の全次数比較へ移す。
規約：底頂点は底の射の像へ移す。空の fiber も含める。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、導来 fiber の標的の同値による比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section

/-- 概要：可換正方形が部分型の頂点 fiber に誘導する射。
方針：引き戻し模型の fiber 射を両側の標準同型で移す。
規約：Kan 性や fibration 性は定義に不要。
使われ方：標的を変更する導来 fiber の実際の比較射。 -/
def vertexFiberSquareMap {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B') (f : E ⟶ E') (g : B ⟶ B')
    (comm : p ≫ g = f ≫ p') (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p' (g.app _ b) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.vertexFiberKanFiberIso p b).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase p p' f g comm b ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.vertexFiberKanFiberIso p' (g.app _ b)).inv

/-- 概要：fiber の正方形の誘導射は全空間の射と包含上で可換。
方針：両同型の包含の式と引き戻し模型の比較の成分計算を使う。
規約：元の可換正方形の射 f そのものを使う。
使われ方：導来 fiber の path 成分と源成分の計算。 -/
lemma vertexFiberSquareMap_ι {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B') (f : E ⟶ E') (g : B ⟶ B')
    (comm : p ≫ g = f ≫ p') (b : B _⦋0⦌) :
    vertexFiberSquareMap p p' f g comm b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p' (g.app _ b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ f := by
  simp only [vertexFiberSquareMap, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.vertexFiberKanFiberIso_inv_ι, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase_ι,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.vertexFiberKanFiberIso_hom_ι]

/-- 概要：Kan fibration の正方形の全空間と底が同値なら各頂点 fiber の誘導射も同値。
方針：既存の全次数の fiber 比較を厳密な模型の同型で前後から合成する。
規約：全空間や fiber の非空性を追加の前提に置かない。
使われ方：比較射の標的を同値で移すときの導来 fiber の同値性。 -/
lemma vertexFiberSquareMap_homotopyEquivalence {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence g)
    (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (vertexFiberSquareMap p p' f g comm b) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.vertexFiberKanFiberIso p b).hom).comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.fibrationFiberMapBase_homotopyEquivalence p p' f g comm hf hg b).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.vertexFiberKanFiberIso p' (g.app _ b)).inv))

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
