module
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornCochainFiller

/-! # 実最後外ホーンの二未知微分方程式の解

概要：指定ホーンから回収した二つの型付き cochain と微分式を、実充填へ渡す一つの解に束ねる。
方針：既知対象族を固定して Q・A の式を保持し、構成した四単体の米田表示を返す。
規約：解の存在は構造のフィールドから推論しない。使われ方：分母消去の代数的解の受入。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 実四次最後外ホーンから回収した二未知 cochain の型付き解。 -/
structure DGFourLastHornSolution (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D) where
  Q : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 3) (-2)
  differential_Q : differential A Q = dgFourLastHornMissingResidual σ
  a : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 4) (-3)
  differential_a : differential A a = dgFourLastHornTopResidual σ +
    compose A ((HornData.knownData σ).edgeHom 3 4 (by decide)) Q (by decide)

variable {σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D} (S : DGFourLastHornSolution σ)

/-- 型付きの解から元の指定四面を持つ実四単体へ。 -/
def DGFourLastHornSolution.simplex : Simplex A D 4 :=
  dgFourLastHornFillerSimplex σ S.Q S.differential_Q S.a S.differential_a

/-- 型付きの解から元のホーン全体を延長する実写像へ。 -/
def DGFourLastHornSolution.extension : Δ[4] ⟶ dgNerve A D :=
  (SSet.yonedaEquiv (X := dgNerve A D)).symm S.simplex

/-- 解から得た実写像は元の指定ホーン全体を厳密に延長する。 -/
lemma DGFourLastHornSolution.fac : (horn 4 4).ι ≫ S.extension = σ :=
  (dgFourLastHornFiller_extension σ S.Q S.differential_Q S.a S.differential_a).symm

end SerrePositivity.InfinityCategories
