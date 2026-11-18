module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainCounit

/-!
# 正規化コチェイン余単位の生成元値

概要：Berger–Fresse §1.1.4・§3.1 の正規化区間の収縮に使う余単位を評価する。
方針：次数延長と single 複体の比較を零次で評価し、鎖の頂点 augmentation へ戻す。
規約：任意の小さい単体集合と任意の可換環。
使われ方：区間の両端点から収縮への合成と、収縮の余代数射性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：整数余単位の零次は鎖の頂点 augmentation（BF §1.1.4）。
方針：extendSingleIso と extendMap の零次公式を使う。
規約：零次成分は singleObjXSelf により A と比較する。
使われ方：正規化零単体の余単位値を計算する。 -/
lemma cochainCounit_zero_apply (X : SSet.{0}) (w : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X 0) :
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A X).f 0
        ((extendXIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) ComplexShape.embeddingDownNat rfl).inv w)) =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.vertexAugmentation A X w := by
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
    ((extendSingleIso ComplexShape.embeddingDownNat (𝟙_ (ModuleCat A)) 0 0 rfl).hom.f 0
      ((extendMap (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit A X) ComplexShape.embeddingDownNat).f 0
        ((extendXIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) ComplexShape.embeddingDownNat rfl).inv w))) = _
  rw [extendSingleIso_hom_f,
    extendMap_f (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit A X) ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply, ChainComplex.single₀ObjXSelf,
    Iso.refl_hom, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit_f_zero]
  change _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.vertexAugmentation A X
    ((extendXIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) ComplexShape.embeddingDownNat rfl).hom
      ((extendXIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) ComplexShape.embeddingDownNat rfl).inv w)) = _
  exact congrArg (fun z => _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.vertexAugmentation A X z)
    (congrArg (fun f => f w)
      (extendXIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) ComplexShape.embeddingDownNat rfl).inv_hom_id)

/-- 概要：正規化零単体の整数余単位値は一（BF §1.1.4）。
方針：零次の比較公式を頂点 augmentation の生成元値に適用する。
規約：係数環の標数を制限しない。
使われ方：区間の端点と収縮の三角形を証明する。 -/
lemma cochainCounit_generator_zero (X : SSet.{0}) (x : X _⦋0⦌) :
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A X).f 0
        ((extendXIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) ComplexShape.embeddingDownNat rfl).inv
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X 0 x))) = (1 : A) := by
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_zero_apply, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.vertexAugmentation_generator]

end SerrePositivity.SimplicialChains.AlexanderWhitney
