module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorHom
public import SerrePositivity.EInfinity.AlexanderWhitney.CochainDiagonal

/-!
# 有限標準単体上の二つの評価の積

DAG XIII §2.2 のスペクトル構造射を、指定された Γ の標準単体で作るための部品。
AW 対角は小さい標準単体だけに適用し、加群の台の宇宙を変更しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 指定された小さい標準単体の AW 対角から、二つの鎖の評価を積にする。 -/
def simplexPairEvaluation {K L : Complex A} (n : SimplexCategory)
    (f : (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n) ⟶ K)
    (g : (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n) ⟶ L) :
    (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n) ⟶ K ⊗ L :=
  AlexanderWhitney.cochainDiagonal A (SSet.stdSimplex.obj n) ≫ (f ⊗ₘ g)

set_option maxHeartbeats 800000 in
-- 正規化 AW と複体のテンソルの同じ型の照合を kernel でも検査するため。
/-- 標準単体の任意の射について、同じ対角を用いた評価は可換する。 -/
lemma simplexPairEvaluation_precomp {K L : Complex A} {n m : SimplexCategory}
    (θ : n ⟶ m)
    (f : (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj m) ⟶ K)
    (g : (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj m) ⟶ L) :
    (BarrattEccles.normalizedFunctor A).map (SSet.stdSimplex.map θ) ≫
      simplexPairEvaluation A m f g =
    simplexPairEvaluation A n
      ((BarrattEccles.normalizedFunctor A).map (SSet.stdSimplex.map θ) ≫ f)
      ((BarrattEccles.normalizedFunctor A).map (SSet.stdSimplex.map θ) ≫ g) := by
  dsimp only [simplexPairEvaluation]
  rw [← Category.assoc, AlexanderWhitney.cochainDiagonal_natural, Category.assoc]
  change AlexanderWhitney.cochainDiagonal A (SSet.stdSimplex.obj n) ≫
    (((BarrattEccles.normalizedFunctor A).map (SSet.stdSimplex.map θ)) ⊗ₘ
      ((BarrattEccles.normalizedFunctor A).map (SSet.stdSimplex.map θ))) ≫ (f ⊗ₘ g) = _
  rw [tensorHom_comp_tensorHom]

/-- 標的の射についても同じ評価を保つ。 -/
lemma simplexPairEvaluation_postcomp {K L K' L' : Complex A} (n : SimplexCategory)
    (f : (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n) ⟶ K)
    (g : (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n) ⟶ L)
    (a : K ⟶ K') (b : L ⟶ L') :
    simplexPairEvaluation A n f g ≫ (a ⊗ₘ b) =
      simplexPairEvaluation A n (f ≫ a) (g ≫ b) := by
  simp only [simplexPairEvaluation, Category.assoc, tensorHom_comp_tensorHom]

end SerrePositivity.EInfinity.PowerOperation
