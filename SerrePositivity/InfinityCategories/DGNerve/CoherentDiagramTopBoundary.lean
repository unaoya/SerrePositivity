module
public import SerrePositivity.InfinityCategories.DGNerve.CoherentDiagramTopHom
/-!
概要：元の coherent 図式の最上成分の HA 右辺を、元の端点を持つ斉次 Hom として保持する。
方針：全頂点集合での実際の有限和に、既存の端点輸送を適用する。
規約：右辺を追加入力にせず、元の単体の HA 係数から計算する。
使われ方：bar の prefix ブロックの内部微分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.DGNerve
open CategoryTheory DifferentialGraded SSet
open scoped Simplicial
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {I : SSet.{u}} (F : (SSet.uliftFunctor.{v, u}).obj I ⟶ dgNerve R C)

def coherentDiagramTopBoundary {n : ℕ} (s : I _⦋n + 1⦌) :
    GradedHom R (coherentDiagramVertex F
      (I.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op s))
      (coherentDiagramVertex F
        (I.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1))).op s))
      (-(n : ℤ) + 1) :=
  gradedHomTransport (coherentDiagramSimplex_obj F s 0)
    (coherentDiagramSimplex_obj F s (Fin.last (n + 1))) rfl
    ((coherentDiagramSimplex F s).toSimplexData.rhs Finset.univ 0 (Fin.last (n + 1))
      (-(n : ℤ)) (coherentDiagramTop_card n) (coherentDiagramTop_min n)
      (coherentDiagramTop_max n) (by simp; omega))

lemma coherentDiagramTop_d {n : ℕ} (s : I _⦋n + 1⦌) :
    differential R (coherentDiagramTop F s) = coherentDiagramTopBoundary F s :=
  coherentDiagramTop_differential F s

end SerrePositivity.InfinityCategories.DGNerve
