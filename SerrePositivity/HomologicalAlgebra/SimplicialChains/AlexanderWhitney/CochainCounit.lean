module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainDiagonal
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.ChainCounit

/-!
# 正規化コチェインの augmentation

概要：Berger–Fresse §1.1.4 の AW 余単位を整数コチェイン模型へ移す。
方針：自然数鎖の augmentation を延長し、単一複体の標準同型を後置する。
規約：終域は既存の整数コチェインテンソルの単位。
使われ方：Barratt–Eccles の既存の augmentation と AW 余単位を同定する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable (A : Type u) [CommRing A]

/-- 概要：AW 余単位の整数コチェイン模型（Berger–Fresse §1.1.4）。
方針：鎖余単位を延長し single 複体の比較同型で単位複体へ移す。
規約：既存のコチェインの単位複体を終域とする。
使われ方：E → Com の augmentation と接続する。 -/
def cochainCounit (X : SSet.{0}) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X ⟶ HomologicalComplex.tensorUnit (ModuleCat A) (.up ℤ) :=
  extendMap (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit A X) ComplexShape.embeddingDownNat ≫
    (extendSingleIso ComplexShape.embeddingDownNat (𝟙_ (ModuleCat A)) 0 0 rfl).hom

/-- 概要：コチェイン余単位は単体集合の射に自然（Berger–Fresse §1.1.4）。
方針：鎖余単位の自然性に延長関手を適用する。
規約：単位複体は一定である。
使われ方：余単位の Σ_n 同変性。 -/
lemma cochainCounit_natural {X Y : SSet.{0}} (f : X ⟶ Y) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A f ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A Y = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A X := by
  change extendMap (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap A f) ComplexShape.embeddingDownNat ≫
      (extendMap (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit A Y) ComplexShape.embeddingDownNat ≫ _) = _
  rw [← Category.assoc, ← extendMap_comp, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit_natural]
  rfl

end SerrePositivity.SimplicialChains.AlexanderWhitney
