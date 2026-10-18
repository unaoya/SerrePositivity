module
public import SerrePositivity.KST.ProExcision.NormalizedStrictificationNaturality
public import SerrePositivity.KST.ProExcision.LinearizedHomotopyOperations

/-!
# 異なる因子間の実厳密化の関手性

概要：二つの異なる区間比較の可換な正方形から、厳密化とその全比較の自然性を導く。
方針：両端と射影の自然性、単体的加群射の加減法を使う。
規約：KST A.5・Lemma 4.16 の (I,a) に関する関手性。
使われ方：環準同型の下で帰納ホモトピーを単体次数ごとに接続する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：実線形区間の射影は任意の単体的写像に自然。
方針：純テンソルの基底で積の自由化と第一射影を評価する。
規約：KST A.3・A.5。使われ方：厳密化の全区間比較の自然性。 -/
lemma linearizedCylinderProjection_naturality {X Y : SSet.{u}} (a : X ⟶ Y) :
    linearizedCylinderMap a ≫ linearizedCylinderProjection Y =
      linearizedCylinderProjection X ≫ linearizedSpaceMap a := by
  apply NatTrans.ext
  funext n
  apply integerTensor_hom_ext
  intro x t
  change (linearizedCylinderProjection Y).app n
    (TensorProduct.tmul ℤ (integerLinearization.map (a.app n) (integerGenerator x)) (integerGenerator t)) = _
  rw [integerLinearization_map_generator]
  change integerLinearization.map ((CartesianMonoidalCategory.fst Y Δ[1]).app n)
    ((integerTensorIso _ _).hom (TensorProduct.tmul ℤ (integerGenerator (a.app n x)) (integerGenerator t))) = _
  rw [integerTensorIso_generator, integerLinearization_map_generator]
  change _ = integerLinearization.map (a.app n)
    (integerLinearization.map ((CartesianMonoidalCategory.fst X Δ[1]).app n)
      ((integerTensorIso _ _).hom (TensorProduct.tmul ℤ (integerGenerator x) (integerGenerator t))))
  rw [integerTensorIso_generator, integerLinearization_map_generator, integerLinearization_map_generator]
  rfl

variable {X X' Y Y' : SSet.{u}}
variable {f e : linearizedSpace X ⟶ linearizedSpace Y}
variable {f' e' : linearizedSpace X' ⟶ linearizedSpace Y'} {m m' : ℕ}
variable (h : LinearizedMHomotopy f e m) (h' : LinearizedMHomotopy f' e' m')
variable (a : X ⟶ X') (b : Y ⟶ Y')
variable (hf : linearizedSpaceMap a ≫ f' = f ≫ linearizedSpaceMap b)
variable (hh : linearizedCylinderMap a ≫ h'.h = h.h ≫ linearizedSpaceMap b)
include hh

/-- 概要：区間比較の自然な正方形は零端点にも自然。
方針：零端点の自然性を前合成する。
規約：KST A.5。使われ方：厳密化の始点補正の自然性。 -/
lemma strictificationEndpoint₀_naturality :
    linearizedSpaceMap a ≫ (linearizedEndpoint₀ X' ≫ h'.h) =
      (linearizedEndpoint₀ X ≫ h.h) ≫ linearizedSpaceMap b := by
  rw [← Category.assoc, linearizedEndpoint₀_naturality, Category.assoc, hh, Category.assoc]

/-- 概要：区間比較の自然な正方形は一端点にも自然。
方針：一端点の自然性を前合成する。
規約：KST A.5。使われ方：厳密化の終点補正の自然性。 -/
lemma strictificationEndpoint₁_naturality :
    linearizedSpaceMap a ≫ (linearizedEndpoint₁ X' ≫ h'.h) =
      (linearizedEndpoint₁ X ≫ h.h) ≫ linearizedSpaceMap b := by
  rw [← Category.assoc, linearizedEndpoint₁_naturality, Category.assoc, hh, Category.assoc]

include hf
/-- 概要：低次厳密化した射は異なる始域と値域の写像に自然。
方針：入力射と両端の自然性を加減する。
規約：KST A.5、因子内のホモトピーの値域を保つ。
使われ方：非可換係数の変更の下での正規化した差のテンソル。 -/
lemma strictifiedMap_naturality :
    linearizedSpaceMap a ≫ h'.strictifiedMap = h.strictifiedMap ≫ linearizedSpaceMap b := by
  simp only [LinearizedMHomotopy.strictifiedMap, Preadditive.comp_add, Preadditive.comp_sub,
    Preadditive.add_comp, Preadditive.sub_comp]
  rw [hf, strictificationEndpoint₀_naturality h h' a b hh, strictificationEndpoint₁_naturality h h' a b hh]

/-- 概要：厳密化への実全区間比較は異なる因子間でも自然。
方針：射影と始点補正の自然性に入力区間の自然性を加える。
規約：KST A.5・4.16、(I,a) の射に適用する。
使われ方：正規化された全鎖比較を関手的にテンソルへ渡す。 -/
lemma strictificationHomotopy_naturality :
    linearizedCylinderMap a ≫ h'.strictificationHomotopy.h =
      h.strictificationHomotopy.h ≫ linearizedSpaceMap b := by
  have h₀ := strictificationEndpoint₀_naturality h h' a b hh
  simp only [LinearizedMHomotopy.strictificationHomotopy, Preadditive.comp_add,
    Preadditive.add_comp, Category.assoc]
  rw [← Category.assoc, linearizedCylinderProjection_naturality, Category.assoc]
  simp only [Preadditive.comp_sub, Preadditive.sub_comp]
  rw [hf, h₀, hh]

end SerrePositivity.KST.ProExcision
