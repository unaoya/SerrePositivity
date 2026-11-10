module
public import SerrePositivity.KST.ProExcision.Lemma416CoefficientData
public import SerrePositivity.KST.ProExcision.CylinderSquareOperations
public import SerrePositivity.KST.ProExcision.Lemma416Homotopy

/-!
# Lemma 4.16 の実帰納ホモトピーの係数関手性

概要：全 m の実ホモトピーは指定元と係数イデアルを保つ環準同型に自然。
方針：因子内の帰納仮定へ A.5 の関手性を適用し、A.6・連結・相殺の自然性を合成する。
規約：KST Lemma 4.16 の非可換再記述と A.5 の augmentation 補正。
使われ方：離散環上の実比較を単体環の各次数に自然に束ねる。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
variable {R R' : Type u} [Ring R] [Ring R']

/-- 概要：実帰納段階のホモトピーは因子内の入力の係数自然性を保つ。
方針：A.5、A.6 の自然性を同じ線形な連結・augmentation 相殺へ適用する。
規約：KST Lemma 4.16、(I,a) の射。結論の自然性を追加仮定にしない。
使われ方：全 m の関手的実ホモトピーの帰納法。 -/
lemma lemma416HomotopyStep_functorial (n m : ℕ) (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J') (a : J) (a' : J') (ha : f (a : R) = (a' : R'))
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap (lastRightColumnHom n m J (a : R)))
      (groupLinearizedMap (1 : Multiplicative (Fin n → J) →* triangularBlockGroup n (m + 1) J)) m)
    (h' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap (lastRightColumnHom n m J' (a' : R')))
      (groupLinearizedMap (1 : Multiplicative (Fin n → J') →* triangularBlockGroup n (m + 1) J')) m)
    (hh : linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ (idealVectorMap J J' (Fin n) f hf))) ≫ h'.h =
      h.h ≫ groupLinearizedMap (triangularBlockGroupMap n (m + 1) J J' f hf)) :
    linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ (idealVectorMap J J' (Fin n) f hf))) ≫
        (lemma416HomotopyStep n m J' a' h').h =
      (lemma416HomotopyStep n m J a h).h ≫ groupLinearizedMap (triangularBlockGroupMap n (m + 2) J J' f hf) := by
  let t := idealVectorMap J J' (Fin n) f hf
  let p := triangularBlockGroupMap n (m + 1) J J' f hf
  let r := triangularBlockGroupMap n (m + 2) J J' f hf
  let d := lemma416GroupData n m J (a : R)
  let d' := lemma416GroupData n m J' (a' : R')
  have hzero := groupZeroMHomotopy_functorial
    (MonoidHom.id (Multiplicative (Fin n → J))) (MonoidHom.id (Multiplicative (Fin n → J'))) t t
    (by intro v; rfl)
  have hA := constructionA5_functorial d d' m 0 h
    (groupZeroMHomotopy (MonoidHom.id (Multiplicative (Fin n → J)))) h'
    (groupZeroMHomotopy (MonoidHom.id (Multiplicative (Fin n → J')))) t p t r
    (lastRightColumnHom_functorial n m J J' f hf a a' ha) (by intro v; rfl)
    (lemma416GroupData_mu_functorial n m J J' f hf a a') hh hzero
  have hC := groupConjugationMHomotopy_functorial
    (auxiliaryBlockColumnHom n m J) (auxiliaryBlockColumnHom n m J') t r
    (auxiliaryBlockColumnHom_functorial n m J J' f hf) (auxiliaryBlockUnit n m J a)
    (auxiliaryBlockUnit n m J' a') (auxiliaryBlockUnit_functorial n m J J' f hf a a' ha) (m + 1)
  have hψ := groupLinearizedMap_square (auxiliaryBlockColumnHom n m J)
    (auxiliaryBlockColumnHom n m J') t r (auxiliaryBlockColumnHom_functorial n m J J' f hf)
  have hφ := groupLinearizedMap_square (lastRightColumnHom n (m + 1) J (a : R))
    (lastRightColumnHom n (m + 1) J' (a' : R')) t r
    (lastRightColumnHom_functorial n (m + 1) J J' f hf a a' ha)
  have hprod := groupLinearizedMap_square d.product d'.product t r
    (lemma416GroupData_product_functorial n m J J' f hf a a' ha)
  have hsum : groupLinearizedMap t ≫
      (groupLinearizedMap (auxiliaryBlockColumnHom n m J') +
        groupLinearizedMap (lastRightColumnHom n (m + 1) J' (a' : R'))) =
    (groupLinearizedMap (auxiliaryBlockColumnHom n m J) +
      groupLinearizedMap (lastRightColumnHom n (m + 1) J (a : R))) ≫ groupLinearizedMap r :=
    cylinderSquare_add hψ hφ
  have hconst := cylinderSquare_constant (nerveMap (SingleObj.mapHom _ _ t)) (groupLinearizedMap r) _ _ hsum
  have hmid := cylinderSquare_constant (nerveMap (SingleObj.mapHom _ _ t)) (groupLinearizedMap r) _ _ hprod
  exact cylinderSquare_sub hconst (cylinderSquare_sub (cylinderSquare_add hC hA) hmid)

/-- 概要：全 m の実帰納ホモトピーは指定元を保つ係数変更に自然。
方針：零次の自然性と帰納段階の自然性を繰り返す。
規約：KST Lemma 4.16 の非可換版の関手性、次数上限は係数次数に依存しない。
使われ方：単体環の各次数の実比較を対角の実 m 次ホモトピーへ移す。 -/
lemma lemma416Homotopy_functorial (n : ℕ) (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J') (a : J) (a' : J') (ha : f (a : R) = (a' : R')) (m : ℕ) :
    linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ (idealVectorMap J J' (Fin n) f hf))) ≫
        (lemma416Homotopy n J' a' m).h =
      (lemma416Homotopy n J a m).h ≫ groupLinearizedMap (triangularBlockGroupMap n (m + 1) J J' f hf) := by
  induction m with
  | zero =>
    exact groupZeroMHomotopy_functorial (lastRightColumnHom n 0 J (a : R))
      (lastRightColumnHom n 0 J' (a' : R')) (idealVectorMap J J' (Fin n) f hf)
      (triangularBlockGroupMap n 1 J J' f hf) (lastRightColumnHom_functorial n 0 J J' f hf a a' ha)
  | succ m ih =>
    exact lemma416HomotopyStep_functorial n m J J' f hf a a' ha
      (lemma416Homotopy n J a m) (lemma416Homotopy n J' a' m) ih

end SerrePositivity.KST.ProExcision
