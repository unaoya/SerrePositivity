module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardModule
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornIndex

/-!
# 標準 Hom の正規化された単体の支持

概要：正規化された標準単体では、全体集合と零番目の面以外の成分は零となる。
方針：正の面を零とする条件を、面を避ける各部分集合へ引き戻して評価する。
規約：Mathlib の正規化と同じく d₁,…,dₙ の核を取る。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の標準模型の正規化複体の計算。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：標準成分の単体の正規化部分加群を定義する。
方針：零次数では全体、正次数では正の面の線形核の共通部分を取る。
規約：零番目の面は微分として残す。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の正規化 Moore 複体との比較。 -/
def standardNormalizedSubmodule (R : Type u) [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
    (x y : D) : ∀ n : ℕ, Submodule R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n)
  | 0 => ⊤
  | n + 1 => ⨅ j : Fin (n + 1), LinearMap.ker
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback (R := R) (x := x) (y := y) (SimplexCategory.δ j.succ).toOrderHom)

/-- 概要：正次数の標準単体が正規化される条件は全ての正の面が零となることである。
方針：部分加群の共通部分と線形核の所属条件を展開する。
規約：全ての正の面を Fin の succ で添字付ける。
使われ方：HA 1.3.1.12 の正規化条件の成分での利用。 -/
lemma mem_standardNormalizedSubmodule_iff {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y (n + 1)) :
    f ∈ standardNormalizedSubmodule R x y (n + 1) ↔
      ∀ j : Fin (n + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback (SimplexCategory.δ j.succ).toOrderHom f = 0 := by
  simp only [standardNormalizedSubmodule, Submodule.mem_iInf, LinearMap.mem_ker]

/-- 概要：正規化された単体の正の頂点を欠く成分は零である。
方針：部分集合を対応する面の像で表し、零となる面の成分を評価する。
規約：成分の集合は非空とし、次数は証明引数で保持する。
使われ方：HA 1.3.1.12 の正規化の有限支持の計算。 -/
lemma normalized_component_zero_of_notMem {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y (n + 1))
    (hf : f ∈ standardNormalizedSubmodule R x y (n + 1)) (j : Fin (n + 1))
    (J : Finset (Fin (n + 2))) (hj : j.succ ∉ J) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) : f.val.component J k hJ hk = 0 := by
  let K := J.preimage j.succ.succAbove j.succ.succAboveOrderEmb.injective.injOn
  have hc : K.card = J.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_preimage J j.succ hj
  have hK : K.Nonempty := Finset.card_pos.mp (by rw [hc]; exact hJ.card_pos)
  have hkK : k = 1 - (K.card : ℤ) := by rw [hc]; exact hk
  have hz := (mem_standardNormalizedSubmodule_iff f).mp hf j
  have hz' := congrArg Subtype.val hz
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_val] at hz'
  have h := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n ↦ s.component K k hK hkK) hz'
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj (SimplexCategory.δ j.succ).toOrderHom
    f.val K k hK hkK j.succ.succAboveOrderEmb.injective.injOn] at h
  have hi : K.image (SimplexCategory.δ j.succ).toOrderHom = J :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.image_preimage J j.succ hj
  have hm (I L : Finset (Fin (n + 2))) (hIL : I = L)
      (hI : I.Nonempty) (hL : L.Nonempty)
      (hki : k = 1 - (I.card : ℤ)) (hkl : k = 1 - (L.card : ℤ)) :
      f.val.component I k hI hki = f.val.component L k hL hkl := by
    subst L
    rfl
  exact (hm _ _ hi _ hJ _ hk).symm.trans h

/-- 概要：正規化された単体の成分は全体集合と零番目の面以外で零である。
方針：この二つ以外の集合は正の頂点を一つ欠くことを使う。
規約：まだ残る二成分の微分による関係は次に計算する。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の正規化複体の全次数での単射性。 -/
lemma normalized_component_zero {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y (n + 1))
    (hf : f ∈ standardNormalizedSubmodule R x y (n + 1))
    (J : Finset (Fin (n + 2))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hfull : J ≠ Finset.univ) (hface : J ≠ Finset.univ.erase 0) :
    f.val.component J k hJ hk = 0 := by
  obtain ⟨j, hj0, hj⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.exists_covering_face J 0).mpr ⟨hfull, hface⟩
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj0
  exact normalized_component_zero_of_notMem f hf j J hj k hJ hk

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
