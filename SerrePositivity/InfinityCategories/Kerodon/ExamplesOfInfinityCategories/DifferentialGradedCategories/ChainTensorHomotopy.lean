module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedAlexanderWhitney
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

/-!
# 整数全テンソルによる鎖ホモトピーの移送

概要：二つの鎖ホモトピーを整数全テンソルのホモトピーへ移す。
方針：双加法関手の二変数それぞれのホモトピー移送を合成する。
規約：KST Construction A.5、ℕ 次数と任意の加群の宇宙。
使われ方：正規化 AW/shuffle の合成で挟まれた Moore 射影・包含を除く。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan

/-- 概要：恒等鎖写像の整数全テンソルは恒等。
方針：全複体の標準包含上でテンソルの恒等則を使う。
規約：KST A.5。使われ方：テンソルへ移したホモトピーの終点の同定。 -/
lemma chainIntegerTensorMap_id (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ) :
    chainIntegerTensorMap (𝟙 K) (𝟙 L) = 𝟙 (chainIntegerTensor K L) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro p q h
  rw [ι_chainIntegerTensorMap]
  change integerTensorMap (𝟙 _) (𝟙 _) ≫ _ = _ ≫ 𝟙 _
  rw [integerTensorMap_id, Category.id_comp, Category.comp_id]

/-- 概要：二つの鎖ホモトピーを整数全テンソルのホモトピーへ移す。
方針：第一変数のホモトピー、第二変数のホモトピーの順に合成する。
規約：KST A.5、実双加法関手に対する標準の全複体。
使われ方：Moore 射影・包含をテンソルから除去する。 -/
def chainIntegerTensorHomotopy
    {K K' L L' : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    {f f' : K ⟶ K'} {g g' : L ⟶ L'} (h : Homotopy f f') (k : Homotopy g g') :
    Homotopy (chainIntegerTensorMap f g) (chainIntegerTensorMap f' g') :=
  (mapBifunctorMapHomotopy₁ h g integerTensorBifunctor (.down ℕ)).trans
    (mapBifunctorMapHomotopy₂ f' k integerTensorBifunctor (.down ℕ))

/-- 概要：両因子の Moore 射影・包含の合成の全テンソルは恒等にホモトピック。
方針：Moore 比較の実ホモトピー同値を各因子で使い、全テンソルへ移す。
規約：KST Construction A.5、正規化は非被約な零次を保つ。
使われ方：正規化した AW→shuffle の実合成の比較。 -/
def chainIntegerTensorMooreRetraction (C D : SimplicialObject (ModuleCat.{u} ℤ)) :
    Homotopy
      (chainIntegerTensorMap
        (PInftyToNormalizedMooreComplex C ≫ inclusionOfMooreComplexMap C)
        (PInftyToNormalizedMooreComplex D ≫ inclusionOfMooreComplexMap D))
      (𝟙 (chainIntegerTensor ((alternatingFaceMapComplex _).obj C)
        ((alternatingFaceMapComplex _).obj D))) :=
  (chainIntegerTensorHomotopy
    (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := C)).homotopyInvHomId
    (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := D)).homotopyInvHomId).trans
      (Homotopy.ofEq (chainIntegerTensorMap_id _ _))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
