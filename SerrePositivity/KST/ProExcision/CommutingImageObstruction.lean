module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IntegerLinearizationDesc
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.Abel

/-!
# 可換な像だけでは消えない二次の bar 鎖

概要：位数8の二面体群の可換な対 (r²,s) の bar 二次サイクルが境界でないことを検証する。
方針：D₁₆→D₈ の中央拡大の carry 二次 cocycle を使い、全512組の cocycle 則を kernel で確認する。
規約：KST Construction A.5 の非可換な標的についての設計検証。ここでは低次 bar 鎖だけを扱い、H_* は定義しない。
使われ方：像の可換性と、ホモトピー全体が可換な二つの係数群内に留まる条件の違いを確認する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.KST.ProExcision
open CategoryTheory DihedralGroup

/-- 概要：位数8の二面体群。方針：Mathlib の回転次数4の群。
規約：D₈ は位数を表す。使われ方：KST A.5 の非可換な標的の検証。 -/
abbrev obstructionDihedral := DihedralGroup 4

/-- 概要：検証に使う90度回転。方針：r 1。
規約：位数4。使われ方：A.5 の二次障害の commutator。 -/
abbrev obstructionRotation : obstructionDihedral := r 1

/-- 概要：検証に使う反射。方針：sr 0。
規約：位数2。使われ方：A.5 の可換な対の第二成分。 -/
abbrev obstructionReflection : obstructionDihedral := sr 0

/-- 概要：検証に使う180度回転。方針：r 2。
規約：中心の元。使われ方：A.5 の可換な対の第一成分。 -/
abbrev obstructionHalfTurn : obstructionDihedral := r 2

/-- 概要：二面体群の回転指数の代表。
方針：r i と sr i の双方で i.val を取る。
規約：0以上4未満。使われ方：中央拡大の carry の定義。 -/
def dihedralExponent : obstructionDihedral → ℕ | r i => i.val | sr i => i.val

/-- 概要：D₁₆→D₈ の中央拡大を検出する二次 cocycle。
方針：回転指数を0以上4未満に戻すときの carry を取る。
規約：値は ℤ/2、正規化した cocycle。使われ方：KST A.5 の二次の bar サイクルの検出。 -/
def dihedralCarryCocycle (x : obstructionDihedral) : obstructionDihedral → ZMod 2
  | r j => ((dihedralExponent x + j.val) / 4 : ℕ)
  | sr j => if j.val < dihedralExponent x then 1 else 0

set_option maxRecDepth 10000 in
/-- 概要：carry は二次 cocycle 則を満たす。
方針：全8³組を通常の decide で kernel 検証する。
規約：追加公理なし。使われ方：KST A.5 の検証で三次境界を零へ送る。 -/
lemma dihedralCarryCocycle_law : ∀ x y z : obstructionDihedral,
    dihedralCarryCocycle x y + dihedralCarryCocycle (x * y) z =
      dihedralCarryCocycle y z + dihedralCarryCocycle x (y * z) := by decide

/-- 概要：単位を含む carry は零。
方針：有限個の組を kernel 検証する。
規約：KST A.5 の非被約な検証。使われ方：定数射と退化単体で検出値が消える。 -/
lemma dihedralCarryCocycle_normalized : ∀ x : obstructionDihedral,
    dihedralCarryCocycle 1 x = 0 ∧ dihedralCarryCocycle x 1 = 0 := by decide

/-- 概要：180度回転と反射は可換。
方針：有限群の積を計算する。
規約：KST A.5 の像の可換条件。使われ方：二次サイクルの境界の零化。 -/
lemma obstructionHalfTurn_commute :
    obstructionHalfTurn * obstructionReflection = obstructionReflection * obstructionHalfTurn := by
  decide

/-- 概要：180度回転は commutator である。
方針：90度回転と反射の commutator を計算する。
規約：KST A.5 の一次の消滅の検証。使われ方：一次の差の明示的な境界の構成。 -/
lemma obstructionHalfTurn_commutator :
    obstructionRotation * obstructionReflection * obstructionRotation⁻¹ * obstructionReflection =
      obstructionHalfTurn := by decide

/-- 概要：非被約 bar の二次境界。
方針：[x|y] を [y]−[xy]+[x] へ線形に送る。
規約：KST A.5 の低次検証。使われ方：可換な対の二次サイクルの確認。 -/
def obstructionBarBoundary₂ :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj (obstructionDihedral × obstructionDihedral) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj obstructionDihedral :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc (fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p.2 - _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (p.1 * p.2) +
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p.1)

/-- 概要：可換な対の標準二次 bar サイクル。
方針：[r²|s]−[s|r²] を取る。
規約：KST A.5 の二次障害。使われ方：carry による非境界の検出。 -/
def obstructionTorusCycle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj (obstructionDihedral × obstructionDihedral) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (obstructionHalfTurn, obstructionReflection) -
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (obstructionReflection, obstructionHalfTurn)

/-- 概要：可換な対の二次 bar 鎖の境界は零。
方針：可換性で積の項を同定し、加減法を相殺する。
規約：KST A.5 の二次障害。使われ方：実際のサイクルであることの確認。 -/
lemma obstructionTorusCycle_boundary : obstructionBarBoundary₂ obstructionTorusCycle = 0 := by
  simp only [obstructionTorusCycle, map_sub, obstructionBarBoundary₂,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator, obstructionHalfTurn_commute]
  abel

/-- 概要：非被約 bar の三次境界。
方針：[x|y|z] を [y|z]−[xy|z]+[x|yz]−[x|y] へ送る。
規約：KST A.5 の低次検証。使われ方：二次鎖が境界でないことの証明。 -/
def obstructionBarBoundary₃ :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj (obstructionDihedral × obstructionDihedral × obstructionDihedral) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj (obstructionDihedral × obstructionDihedral) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc (fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (p.2.1, p.2.2) -
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (p.1 * p.2.1, p.2.2) + _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (p.1, p.2.1 * p.2.2) -
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (p.1, p.2.1))

/-- 概要：二次 bar 鎖を carry で評価する線形写像。
方針：二次 cocycle の基底上の評価を整数線形に拡張する。
規約：KST A.5 の低次検証。使われ方：三次境界を消し、可換な対のサイクルを検出する。 -/
def obstructionCocycleEvaluation :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj (obstructionDihedral × obstructionDihedral) ⟶ ModuleCat.of ℤ (ZMod 2) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc (fun p ↦ dihedralCarryCocycle p.1 p.2)

/-- 概要：carry の評価は全ての三次境界を零へ送る。
方針：自由加群の基底上で cocycle 則を適用する。
規約：KST A.5 の低次検証。使われ方：非境界の厳密な証明。 -/
lemma obstructionCocycleEvaluation_boundary : obstructionBarBoundary₃ ≫ obstructionCocycleEvaluation = 0 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
  rintro ⟨x, y, z⟩
  change obstructionCocycleEvaluation (obstructionBarBoundary₃ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (x, y, z))) = 0
  simp only [obstructionBarBoundary₃, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator,
    map_add, map_sub, obstructionCocycleEvaluation]
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator]
  change dihedralCarryCocycle y z - dihedralCarryCocycle (x * y) z +
    dihedralCarryCocycle x (y * z) - dihedralCarryCocycle x y = 0
  calc
    _ = (dihedralCarryCocycle y z + dihedralCarryCocycle x (y * z)) -
      (dihedralCarryCocycle x y + dihedralCarryCocycle (x * y) z) := by abel
    _ = 0 := by rw [← dihedralCarryCocycle_law, sub_self]

/-- 概要：可換な対の二次サイクルの carry 評価は1。
方針：二つの基底で評価して有限群の carry を計算する。
規約：KST A.5 の二次障害。使われ方：非境界の検出。 -/
lemma obstructionCocycleEvaluation_torus : obstructionCocycleEvaluation obstructionTorusCycle = 1 := by
  simp only [obstructionTorusCycle, map_sub, obstructionCocycleEvaluation]
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator]
  decide

/-- 概要：可換な対の二次サイクルは三次境界でない。
方針：carry で評価すると境界は0、指定したサイクルは1となる。
規約：KST A.5 の非可換な標的での設計検証。H_* の定義は導入しない。
使われ方：augmentation 補正だけで一般の非可換な A.5 を定理化しないための検証。 -/
theorem obstructionTorusCycle_not_boundary : ¬ ∃ v, obstructionBarBoundary₃ v = obstructionTorusCycle := by
  rintro ⟨v, hv⟩
  have he := congrArg (fun q ↦ q.hom v) obstructionCocycleEvaluation_boundary
  change obstructionCocycleEvaluation (obstructionBarBoundary₃ v) = 0 at he
  rw [hv, obstructionCocycleEvaluation_torus] at he
  exact one_ne_zero he

/-- 概要：commutator の一次の差を埋める明示的な二次 bar 鎖。
方針：commutator の語の三角形の和と、逆元・単位の項を組み合わせる。
規約：KST A.5 の一次の消滅の検証。非被約な単位の項を残す。
使われ方：[r²]−[1] が境界であることの確認。 -/
def obstructionHalfTurnBoundingChain :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj (obstructionDihedral × obstructionDihedral) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (obstructionRotation, obstructionRotation⁻¹) +
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (obstructionReflection, obstructionReflection) -
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (obstructionRotation, obstructionReflection) -
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (obstructionRotation * obstructionReflection, obstructionRotation⁻¹) -
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (obstructionRotation * obstructionReflection * obstructionRotation⁻¹,
      obstructionReflection) + _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (1, 1)

/-- 概要：commutator の一次の差は指定した二次鎖の境界。
方針：bar の境界を展開し、群の逆元則と commutator の計算で相殺する。
規約：KST A.5 の一次と二次の障害の区別。使われ方：設計確認の紙の反例の一次入力。 -/
lemma obstructionHalfTurnBoundingChain_boundary :
    obstructionBarBoundary₂ obstructionHalfTurnBoundingChain =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator obstructionHalfTurn - _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (1 : obstructionDihedral) := by
  simp only [obstructionHalfTurnBoundingChain, map_add, map_sub, obstructionBarBoundary₂,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator, mul_inv_cancel,
    show obstructionReflection * obstructionReflection = 1 from by decide,
    obstructionHalfTurn_commutator, one_mul]
  abel

end SerrePositivity.KST.ProExcision
