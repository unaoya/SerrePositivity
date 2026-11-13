module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.SphericalCochain
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.SkeletalAttachmentPushout

/-!
概要：骨格上で低次元を定数に送る射のセルごとの延長障害。
方針：骨格の単体の持ち上げから正規化 cochain を作り、各セルの境界充填を交代微分で判定する。
規約：Mathlib の skeleton d は次元 d 未満。射は通常の n+2 骨格上にある。
使われ方：Goerss–Jardine I §7、VIII §1。幾何的な延長障害と交代微分の比較。

対応節は Kerodon 1.1（Tag 0004）。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalSphericalCochain
end SerrePositivity.KST.Spectra.SkeletalSphericalCochain
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
open _root_.SerrePositivity.KST.Spectra.SkeletalSphericalCochain

noncomputable section

variable {K X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
  (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ X)
  (h : ∀ s : (K.skeleton (n + 3) : SSet.{u}) _⦋n + 1⦌,
    yonedaEquiv.symm s ≫ f = SSet.const x)

/-- 概要：骨格上の射の単体の像を境界定数単体へ送る。
方針：骨格に必ず属する単体を持ち上げ、低次元で定数の射の像を使う。
規約：単体の実際の次元は n + 2。
使われ方：Goerss–Jardine I §7、VIII §1。セルの境界上の係数。 -/
def simplexValue (s : K _⦋n + 2⦌) : X.PtSimplex (n + 2) x :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplexValue f h ⟨s, K.mem_skeleton s⟩

/-- 概要：骨格上の射の退化単体の像の代表は定数。
方針：骨格の単体の持ち上げは退化と可換なので、全体の射の退化計算を使う。
規約：代表単体そのものの等式。
使われ方：Goerss–Jardine III §2、VIII §1。正規化された係数の零性。 -/
theorem simplexValue_degeneracy (s : K _⦋n + 1⦌) (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue f h (K.σ i s) = .const :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplexValue_degeneracy f h ⟨s, K.mem_skeleton s⟩ i

variable [KanComplex X]

/-- 概要：骨格上の射の非退化単体ごとのホモトピー類。
方針：像の境界定数単体を高次の可換ホモトピー群へ送る。
規約：cochain の次数と係数の実際の次数はともに n + 2。
使われ方：Goerss–Jardine VIII §1。セルの延長障害の入力。 -/
def cochain : K.nonDegenerate (n + 2) → Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x) :=
  fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue f h s.val)

/-- 概要：骨格の係数を零延長すると任意の単体の像の類になる。
方針：退化単体を一つの退化として表し、その像が定数であることを使う。
規約：正規化 cochain の零延長。
使われ方：Goerss–Jardine III §2、VIII §1。セル境界の全ての面の寄与。 -/
theorem zeroExtend_cochain (s : K _⦋n + 2⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.zeroExtend K
      (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x))) (n + 2)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain f h) s = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue f h s) := by
  classical
  unfold _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.zeroExtend
  split_ifs with hs
  · rfl
  · have hd : s ∈ K.degenerate (n + 2) := (K.mem_degenerate_iff_notMem_nonDegenerate s).2 hs
    rw [K.degenerate_eq_iUnion_range_σ] at hd
    obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hd
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue_degeneracy, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass_const]

/-- 概要：骨格上の射の次のセルへの延長障害は通常の交代微分。
方針：各面の値への零延長の式を正規化微分へ適用する。
規約：セルは非退化な n+3 単体。
使われ方：Goerss–Jardine VIII §1。幾何的な境界の交代和との厳密な式。 -/
theorem differential_cochain_apply (s : K.nonDegenerate (n + 3)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
      (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x))) (n + 2)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain f h) s =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue f h (K.δ j s.val)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential_apply]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.zeroExtend_cochain]
  rfl

/-- 概要：骨格上の射の一つの新規セルの境界は微分が零のとき丁度充填できる。
方針：球面的境界の充填判定を、そのセルの全ての面の像へ適用する。
規約：境界射は指定した面族の実際の貼り合わせ。
使われ方：Goerss–Jardine I §7、VIII §1。幾何的な延長障害のセルごとの判定。 -/
theorem cell_filler_iff (s : K.nonDegenerate (n + 3)) :
    (∃ φ : (Δ[n + 3] : SSet.{u}) ⟶ X,
      (boundary (n + 3)).ι ≫ φ =
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.boundaryMap (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue f h (K.δ j s.val))) ↔
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x))) (n + 2)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain f h) s = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.differential_cochain_apply]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.boundary_filler_iff _

end

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletalSphericalCochain.cell_filler_iff := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cell_filler_iff

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletalSphericalCochain.cochain := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletalSphericalCochain.differential_cochain_apply := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.differential_cochain_apply

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletalSphericalCochain.simplexValue := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletalSphericalCochain.simplexValue_degeneracy := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue_degeneracy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletalSphericalCochain.zeroExtend_cochain := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.zeroExtend_cochain

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletalSphericalCochain.cochain.congr_simp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain.congr_simp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletalSphericalCochain.simplexValue._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletalSphericalCochain.simplexValue._proof_3 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletalSphericalCochain.simplexValue.congr_simp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue.congr_simp
