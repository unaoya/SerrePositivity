module


public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.NormalizedCochainCoefficientMaps
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Grp.Colimits

/-!
概要：通常の加法的係数を値とする非退化単体の正規化 cochain。
方針：ULift ℤ からの加法群の射を係数の元に移し、交代微分を共役する。
規約：係数の加法群は任意。Hom 係数ではなく元の係数の値で式を述べる。
使われ方：Goerss–Jardine III §2、VIII §1。ホモトピー群係数の交代式の比較先。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.NormalizedValueCochains
end SerrePositivity.KST.Spectra.NormalizedValueCochains
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains
open _root_.SerrePositivity.KST.Spectra.NormalizedValueCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：整数の単位係数からの Hom の cochain と係数の元の cochain の加法同型。
方針：各座標で ULift ℤ からの射を一の像に移す標準同型を使う。
規約：単体集合と係数群は同じ宇宙。
使われ方：Goerss–Jardine III §2。通常の係数を持つ cochain の表示。 -/
def coefficientEquiv (K : SSet.{u}) (M : AddCommGrpCat.{u}) (n : ℕ) :
    (K.nonDegenerate n → (AddCommGrpCat.of (ULift.{u} ℤ) ⟶ M)) ≃+
      (K.nonDegenerate n → M) where
  toFun a s := AddCommGrpCat.uliftZMultiplesAddEquiv M (a s)
  invFun a s := (AddCommGrpCat.uliftZMultiplesAddEquiv M).symm (a s)
  left_inv a := by
    funext s
    exact (AddCommGrpCat.uliftZMultiplesAddEquiv M).symm_apply_apply _
  right_inv a := by
    funext s
    exact (AddCommGrpCat.uliftZMultiplesAddEquiv M).apply_symm_apply _
  map_add' a b := by
    funext s
    exact map_add (AddCommGrpCat.uliftZMultiplesAddEquiv M) _ _

def zeroExtend (K : SSet.{u}) (M : AddCommGrpCat.{u}) (n : ℕ)
    (a : K.nonDegenerate n → M) (s : K _⦋n⦌) : M := by
  classical
  exact if hs : s ∈ K.nonDegenerate n then a ⟨s, hs⟩ else 0

lemma coefficientEquiv_zeroExtend (K : SSet.{u}) (M : AddCommGrpCat.{u}) (n : ℕ)
    (a : K.nonDegenerate n → M) (s : K _⦋n⦌) :
    AddCommGrpCat.uliftZMultiplesAddEquiv M
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.zeroExtend K (AddCommGrpCat.of (ULift.{u} ℤ)) M n
        ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.coefficientEquiv K M n).symm a) s) = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.zeroExtend K M n a s := by
  classical
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.zeroExtend, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.zeroExtend]
  split_ifs with hs
  · exact (AddCommGrpCat.uliftZMultiplesAddEquiv M).apply_symm_apply _
  · exact map_zero _

/-- 概要：係数の元を値とする正規化 cochain の通常の微分。
方針：正規化鎖の Hom の微分から得た交代微分を係数の値の表示へ移す。
規約：骨格の微分と一致するとはまだ主張しない。
使われ方：Goerss–Jardine VIII §1。高次ホモトピー群係数の比較先の微分。 -/
def differential (K : SSet.{u}) (M : AddCommGrpCat.{u}) (n : ℕ) :
    (K.nonDegenerate n → M) →+ (K.nonDegenerate (n + 1) → M) :=
  (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.coefficientEquiv K M (n + 1)).toAddMonoidHom.comp
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.differential K (AddCommGrpCat.of (ULift.{u} ℤ)) M n).comp
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.coefficientEquiv K M n).symm.toAddMonoidHom)

/-- 概要：正規化 cochain 微分は退化面で零に延長した係数の交代和。
方針：Hom 係数の交代式を加法同型の有限和と整数倍の保存で移す。
規約：標準の面の順序の符号 (-1)^i を使う。
使われ方：Goerss–Jardine III §2、VIII §1。球面の向きと照合する通常の式。 -/
lemma differential_apply (K : SSet.{u}) (M : AddCommGrpCat.{u}) (n : ℕ)
    (a : K.nonDegenerate n → M) (s : K.nonDegenerate (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K M n a s =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.zeroExtend K M n a (K.δ i s.val) := by
  change AddCommGrpCat.uliftZMultiplesAddEquiv M
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.differential K (AddCommGrpCat.of (ULift.{u} ℤ)) M n
      ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.coefficientEquiv K M n).symm a) s) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.differential_apply]
  simp only [map_sum, map_zsmul, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.coefficientEquiv_zeroExtend]

@[simp]
lemma differential_comp (K : SSet.{u}) (M : AddCommGrpCat.{u}) (n : ℕ)
    (a : K.nonDegenerate n → M) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K M (n + 1) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K M n a) = 0 := by
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.coefficientEquiv K M (n + 2)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.differential K (AddCommGrpCat.of (ULift.{u} ℤ)) M (n + 1)
      ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.coefficientEquiv K M (n + 1)).symm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.coefficientEquiv K M (n + 1)
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.differential K (AddCommGrpCat.of (ULift.{u} ℤ)) M n
          ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.coefficientEquiv K M n).symm a))))) = 0
  rw [AddEquiv.symm_apply_apply, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.differential_comp, map_zero]

end

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
