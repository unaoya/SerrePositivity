module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DGNerveBasic
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LowDimensional
/-!
概要：任意の元の dg nerve 値図式から、同じ対象族と単体ごとの HA データを取り出す。
方針：指定図式の全単体と自然性を評価し、各頂点の元の対象との厳密な等号を保持する。
規約：図式を通常の h 圏へ落とさず、対象の Small 性も要求しない。
使われ方：D-8 c2 の filtered 加群図式の実係数計算。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {I : SSet.{u}} (F : (SSet.uliftFunctor.{v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)

def coherentDiagramSimplex {n : ℕ} (s : I _⦋n⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n :=
  F.app _ (ULift.up s)

def coherentDiagramVertex (i : I _⦋0⦌) : C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (coherentDiagramSimplex F i)

lemma coherentDiagramSimplex_map {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (s : I _⦋n⦌) :
    coherentDiagramSimplex F (I.map (SimplexCategory.mkHom α).op s) =
      (coherentDiagramSimplex F s).pullback α := by
  have h := ConcreteCategory.congr_hom (F.naturality (SimplexCategory.mkHom α).op)
    (ULift.up.{v, u} s)
  exact h

lemma coherentDiagramSimplex_obj {n : ℕ} (s : I _⦋n⦌) (j : Fin (n + 1)) :
    (coherentDiagramSimplex F s).obj j = coherentDiagramVertex F
      (I.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ j).op s) := by
  have h := coherentDiagramSimplex_map F (m := 0) (OrderHom.const (Fin 1) j) s
  exact (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 0 => t.obj 0) h).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
