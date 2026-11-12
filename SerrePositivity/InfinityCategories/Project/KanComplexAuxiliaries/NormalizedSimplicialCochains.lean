module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

/-!
概要：非退化単体上の cochain の交代微分を正規化鎖複体の Hom から与える。
方針：Mathlib の非退化単体の余積の普遍性で Hom を関数群へ移す。
規約：借りるのは通常の正規化鎖複体とその表示だけ。H_* の新しい定理は宣言しない。
使われ方：Goerss–Jardine III §2、VIII §1。幾何的微分の比較先となる正規化 cochain。
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.NormalizedSimplicialCochains
end SerrePositivity.KST.Spectra.NormalizedSimplicialCochains
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains
open _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  (K : SSet.{w}) (R M : C)

/-- 概要：非退化単体ごとの係数射を正規化鎖群からの射へ延長する。
方針：Mathlib の非退化単体の余積の普遍性で降下する。
規約：係数は任意の前加法圏の Hom 群。
使われ方：Goerss–Jardine III §2。正規化 cochain の表示。 -/
def extend (n : ℕ) (a : K.nonDegenerate n → (R ⟶ M)) :
    (K.normalizedChainComplex R).X n ⟶ M :=
  (K.isColimitCofanNormalizedChainComplex R n).desc (Cofan.mk M a)

@[reassoc]
lemma inclusion_extend (n : ℕ) (a : K.nonDegenerate n → (R ⟶ M)) (s : K.nonDegenerate n) :
    K.ιNormalizedChainComplex s.val ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.extend K R M n a = a s :=
  (K.isColimitCofanNormalizedChainComplex R n).fac (Cofan.mk M a) (Discrete.mk s)

/-- 概要：正規化鎖群からの Hom は非退化単体上の係数の関数群。
方針：各生成子への制限と余積からの延長を互いの逆にする。
規約：加法は係数の Hom 群の加法。
使われ方：Goerss–Jardine III §2、VIII §1。交代 cochain 微分の移送。 -/
def coefficientEquiv (n : ℕ) :
    ((K.normalizedChainComplex R).X n ⟶ M) ≃+ (K.nonDegenerate n → (R ⟶ M)) where
  toFun f s := K.ιNormalizedChainComplex s.val ≫ f
  invFun := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.extend K R M n
  left_inv f := by
    apply K.normalizedChainComplex_hom_ext
    intro s hs
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.inclusion_extend K R M n _ ⟨s, hs⟩
  right_inv a := by
    funext s
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.inclusion_extend K R M n a s
  map_add' f g := by
    funext s
    exact Preadditive.comp_add _ _ _ _ f g

/-- 概要：非退化単体の cochain を退化単体で零に延長した値。
方針：非退化性の判定で場合分けする。
規約：全単体上の関数に戻して交代面の和を取る。
使われ方：Goerss–Jardine III §2。正規化された cochain の明示式。 -/
def zeroExtend (n : ℕ) (a : K.nonDegenerate n → (R ⟶ M)) (s : K _⦋n⦌) : R ⟶ M := by
  classical
  exact if hs : s ∈ K.nonDegenerate n then a ⟨s, hs⟩ else 0

lemma inclusion_extend_all (n : ℕ) (a : K.nonDegenerate n → (R ⟶ M)) (s : K _⦋n⦌) :
    K.ιNormalizedChainComplex s ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.extend K R M n a = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.zeroExtend K R M n a s := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.zeroExtend]
  split_ifs with hs
  · exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.inclusion_extend K R M n a ⟨s, hs⟩
  · rw [K.ιNormalizedChainComplex_eq_zero s (by simpa only [SSet.nonDegenerate,
        Set.mem_compl_iff, not_not] using hs), zero_comp]

/-- 概要：正規化鎖複体の微分への前合成による cochain 微分。
方針：鎖の微分の向きを Hom で反転する。
規約：cochain の次数は n から n+1 へ上がる。
使われ方：Goerss–Jardine III §2、VIII §1。正規化 cochain の複体条件。 -/
def homDifferential (n : ℕ) :
    ((K.normalizedChainComplex R).X n ⟶ M) →+
      ((K.normalizedChainComplex R).X (n + 1) ⟶ M) where
  toFun f := (K.normalizedChainComplex R).d (n + 1) n ≫ f
  map_zero' := comp_zero
  map_add' f g := Preadditive.comp_add _ _ _ _ f g

lemma homDifferential_comp (n : ℕ) (f : (K.normalizedChainComplex R).X n ⟶ M) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.homDifferential K R M (n + 1) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.homDifferential K R M n f) = 0 := by
  change (K.normalizedChainComplex R).d (n + 2) (n + 1) ≫
    ((K.normalizedChainComplex R).d (n + 1) n ≫ f) = 0
  rw [← Category.assoc, HomologicalComplex.d_comp_d, zero_comp]

/-- 概要：非退化単体の係数群の正規化 cochain 微分。
方針：正規化鎖群の Hom の微分を生成子による加法同型で共役する。
規約：幾何的な骨格の微分との一致は別途証明する。
使われ方：Goerss–Jardine VIII §1。比較先の通常の cochain 微分。 -/
def differential (n : ℕ) : (K.nonDegenerate n → (R ⟶ M)) →+
    (K.nonDegenerate (n + 1) → (R ⟶ M)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.coefficientEquiv K R M (n + 1)).toAddMonoidHom.comp
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.homDifferential K R M n).comp (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.coefficientEquiv K R M n).symm.toAddMonoidHom)

/-- 概要：正規化 cochain 微分は退化面を零とする交代面の和。
方針：Mathlib の正規化鎖の生成子の微分式を Hom の係数へ送る。
規約：各面の符号は (-1)^i。
使われ方：Goerss–Jardine III §2、VIII §1。骨格の幾何的微分と照合する式。 -/
lemma differential_apply (n : ℕ) (a : K.nonDegenerate n → (R ⟶ M))
    (s : K.nonDegenerate (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.differential K R M n a s =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.zeroExtend K R M n a (K.δ i s.val) := by
  change K.ιNormalizedChainComplex s.val ≫
    ((K.normalizedChainComplex R).d (n + 1) n ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.extend K R M n a) = _
  rw [← Category.assoc, K.ιNormalizedChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.inclusion_extend_all]

@[simp]
lemma differential_comp (n : ℕ) (a : K.nonDegenerate n → (R ⟶ M)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.differential K R M (n + 1) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.differential K R M n a) = 0 := by
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.coefficientEquiv K R M (n + 2)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.homDifferential K R M (n + 1) ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.coefficientEquiv K R M (n + 1)).symm
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.coefficientEquiv K R M (n + 1) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.homDifferential K R M n
        ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.coefficientEquiv K R M n).symm a))))) = 0
  rw [AddEquiv.symm_apply_apply, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.homDifferential_comp, map_zero]

end

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.coefficientEquiv (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.coefficientEquiv := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.coefficientEquiv

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.differential (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.differential := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.differential

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.differential_apply := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.differential_apply

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.differential_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.differential_comp

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.extend (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.extend := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.extend

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.homDifferential (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.homDifferential := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.homDifferential

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.homDifferential_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.homDifferential_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.inclusion_extend := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.inclusion_extend

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.inclusion_extend_all := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.inclusion_extend_all

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.inclusion_extend_assoc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.inclusion_extend_assoc

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.zeroExtend (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.zeroExtend := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.zeroExtend

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.coefficientEquiv._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.coefficientEquiv._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.coefficientEquiv._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.coefficientEquiv._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.coefficientEquiv._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.coefficientEquiv._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.coefficientEquiv._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.coefficientEquiv._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.homDifferential._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.homDifferential._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.NormalizedSimplicialCochains.homDifferential._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedSimplicialCochains.homDifferential._proof_2
