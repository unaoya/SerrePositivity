module

public import SerrePositivity.EInfinity.IntervalCuts.DegreeOneDeletions
public import SerrePositivity.EInfinity.IntervalCuts.Components
public import SerrePositivity.EInfinity.IntervalCuts.TensorBoundaryValues
public import SerrePositivity.EInfinity.Surjection.DeletionDifferential

/-!
# 実際の頂点成分の微分保存

概要：Berger–Fresse §2.2.7 の区間切断の頂点成分は実際の削除微分を保つ。
方針：次数一から零への微分は反復色の二係数を相殺し、高い次数は頂点成分の零性を使う。
規約：零次数の頂点テンソルは実際の反復テンソルの閉じた元。
使われ方：辺成分の微分保存と合わせて余演算を複体射へ束ねる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped BigOperators

variable (A : Type u) [CommRing A]

/-- 概要：零次数の全射語の生成元は同じ頂点の反復テンソルへ移る（BF §2.2.6）。
方針：等濃度の全射は単射なので実際の非退化基底語として評価する。
規約：arity 零も含む。
使われ方：次数一の二削除を同じ頂点値へ送る。 -/
lemma vertexComponent_generator_zero_degree {n : ℕ} (v : Fin n → Fin n)
    (hs : Function.Surjective v) (b : Fin 2) :
    vertexComponent A n 0 b (generator A (d := 0) v) =
      tensorVectorOfDegree A n 0 (fun _ => vertex b) (vertex_tupleDegree n b) := by
  have hi : Function.Injective v :=
    ((Fintype.bijective_iff_surjective_and_card v).mpr ⟨hs, by simp⟩).1
  let u : BasisWord n 0 := ⟨v, hs, nondegenerate_of_injective hi⟩
  rw [show generator A (d := 0) v = basis A n 0 (ULift.up u) from generator_word A u,
    vertexComponent_basis]
  simp [vertexComponentOnWord]

/-- 概要：次数一の語の削除微分の零次数頂点成分は零（BF §1.2.3・§2.2.7）。
方針：唯一の反復色の +1・−1 の二削除を同じ頂点テンソルへ送って相殺する。
規約：それ以外の削除係数は全て零。
使われ方：頂点での微分保存の唯一の非自明な次数。 -/
lemma vertexComponent_differentialOnWord_degree_one {n : ℕ} (u : BasisWord n 1)
    (v : Fin 2) : vertexComponent A n 0 v (differentialOnWord A u) = 0 := by
  classical
  obtain ⟨a, b, hab, hu, hca, hcb, hzero⟩ := degreeOne_deletion_pair u
  have hsa : Function.Surjective (erase u.val a) :=
    (erase_surjective_iff u.val u.surjective a).mpr ⟨b, ne_of_gt hab, hu.symm⟩
  have hsb : Function.Surjective (erase u.val b) :=
    (erase_surjective_iff u.val u.surjective b).mpr ⟨a, ne_of_lt hab, hu⟩
  let F (i : Fin (n + 1)) :=
    deletionCoefficient u.val i • vertexComponent A n 0 v (generator A (d := 0) (erase u.val i))
  have hs : (∑ i, F i) = F a + F b := by
    rw [← Finset.add_sum_erase Finset.univ F (Finset.mem_univ a),
      ← Finset.add_sum_erase (Finset.univ.erase a) F
        (Finset.mem_erase.mpr ⟨ne_of_gt hab, Finset.mem_univ b⟩)]
    have hz : (∑ i ∈ (Finset.univ.erase a).erase b, F i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hib := (Finset.mem_erase.mp hi).1
      have hia := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      simp only [F, hzero i hia hib, zero_smul]
    rw [hz, add_zero]
  simp only [differentialOnWord, map_sum, map_zsmul]
  change (∑ i, F i) = 0
  rw [hs]
  simp only [F, hca, hcb, one_smul, neg_one_zsmul,
    vertexComponent_generator_zero_degree A _ hsa v,
    vertexComponent_generator_zero_degree A _ hsb v, add_neg_cancel]

/-- 概要：正次数の全射語加群に対する頂点線形成分は零写像（BF §2.2.6）。
方針：実際の自由基底の全像が零であることを使う。
規約：任意の可換環と arity。
使われ方：高次数での頂点微分保存を直ちに解く。 -/
lemma vertexComponent_eq_zero_of_positive (n d : ℕ) (b : Fin 2) (hd : 0 < d) :
    vertexComponent A n d b = 0 := by
  apply (basis A n d).ext
  intro u
  rw [vertexComponent_basis, LinearMap.zero_apply]
  exact vertexComponentOnWord_eq_zero_of_positive A u.down hd b

/-- 概要：全正次数の語の削除微分の実際の頂点成分は零（BF §2.2.7）。
方針：次数一の二項相殺と、それ以上の頂点線形成分の零性を使う。
規約：削除微分は非全射・退化生成元も元の定義通り含む。
使われ方：余演算の頂点生成元に対する複体射条件。 -/
lemma vertexComponent_differentialOnWord {n d : ℕ} (u : BasisWord n (d + 1)) (b : Fin 2) :
    vertexComponent A n d b (differentialOnWord A u) = 0 := by
  cases d with
  | zero => exact vertexComponent_differentialOnWord_degree_one A u b
  | succ d =>
    rw [vertexComponent_eq_zero_of_positive A n (d + 1) b (by omega), LinearMap.zero_apply]

/-- 概要：実際の全頂点成分の出力は閉じている（BF §2.2.7）。
方針：次数零では頂点テンソルの微分零、正次数では成分自身の零性を使う。
規約：全 arity・全語次数・両頂点。
使われ方：余演算の頂点生成元の標的微分。 -/
lemma vertexComponentOnWord_d_eq_zero {n d : ℕ} (u : BasisWord n d) (b : Fin 2) :
    (power (interval A) n).d (-(d : ℤ)) (-(d : ℤ) + 1) (vertexComponentOnWord A u b) = 0 := by
  cases d with
  | zero =>
    simpa only [vertexComponentOnWord, dite_eq_left rfl] using!
      tensorVectorOfDegree_d_eq_zero A n 0 (fun _ => vertex b) (vertex_tupleDegree n b)
        (tensorVector_d_eq_zero_of_vertices A n (fun _ => b))
  | succ d =>
    rw [vertexComponentOnWord_eq_zero_of_positive A u (by omega) b, map_zero]

/-- 概要：正次数の実際の頂点成分は削除微分と可換（BF §2.2.7）。
方針：元の正次数頂点成分と削除微分の頂点成分がともに零であることを使う。
規約：標的次数を実際の削除後次数へ揃える。
使われ方：χ の区間余演算を実際の複体射へ束ねる。 -/
lemma vertexComponentOnWord_d_positive {n d : ℕ} (u : BasisWord n (d + 1)) (b : Fin 2) :
    (power (interval A) n).d (-((d + 1 : ℕ) : ℤ)) (-(d : ℤ))
        (vertexComponentOnWord A u b) = vertexComponent A n d b (differentialOnWord A u) := by
  rw [vertexComponentOnWord_eq_zero_of_positive A u (by omega) b, map_zero,
    vertexComponent_differentialOnWord A u b]

end SerrePositivity.EInfinity.IntervalCuts
