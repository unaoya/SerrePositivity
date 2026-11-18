module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.DegreeOneDeletions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Components
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorBoundaryValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DeletionDifferential

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable (A : Type u) [CommRing A]

/-- 概要：零次数の全射語の生成元は同じ頂点の反復テンソルへ移る（BF §2.2.6）。
方針：等濃度の全射は単射なので実際の非退化基底語として評価する。
規約：arity 零も含む。
使われ方：次数一の二削除を同じ頂点値へ送る。 -/
lemma vertexComponent_generator_zero_degree {n : ℕ} (v : Fin n → Fin n)
    (hs : Function.Surjective v) (b : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent A n 0 b (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (d := 0) v) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n 0 (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_tupleDegree n b) := by
  have hi : Function.Injective v :=
    ((Fintype.bijective_iff_surjective_and_card v).mpr ⟨hs, by simp⟩).1
  let u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n 0 := ⟨v, hs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.nondegenerate_of_injective hi⟩
  rw [show _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (d := 0) v = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n 0 (ULift.up u) from _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_word A u,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_basis]
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponentOnWord]

/-- 概要：次数一の語の削除微分の零次数頂点成分は零（BF §1.2.3・§2.2.7）。
方針：唯一の反復色の +1・−1 の二削除を同じ頂点テンソルへ送って相殺する。
規約：それ以外の削除係数は全て零。
使われ方：頂点での微分保存の唯一の非自明な次数。 -/
lemma vertexComponent_differentialOnWord_degree_one {n : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n 1)
    (v : Fin 2) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent A n 0 v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differentialOnWord A u) = 0 := by
  classical
  obtain ⟨a, b, hab, hu, hca, hcb, hzero⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.degreeOne_deletion_pair u
  have hsa : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val a) :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_surjective_iff u.val u.surjective a).mpr ⟨b, ne_of_gt hab, hu.symm⟩
  have hsb : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val b) :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_surjective_iff u.val u.surjective b).mpr ⟨a, ne_of_lt hab, hu⟩
  let F (i : Fin (n + 1)) :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u.val i • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent A n 0 v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (d := 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val i))
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
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differentialOnWord, map_sum, map_zsmul]
  change (∑ i, F i) = 0
  rw [hs]
  simp only [F, hca, hcb, one_smul, neg_one_zsmul,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_generator_zero_degree A _ hsa v,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_generator_zero_degree A _ hsb v, add_neg_cancel]

/-- 概要：正次数の全射語加群に対する頂点線形成分は零写像（BF §2.2.6）。
方針：実際の自由基底の全像が零であることを使う。
規約：任意の可換環と arity。
使われ方：高次数での頂点微分保存を直ちに解く。 -/
lemma vertexComponent_eq_zero_of_positive (n d : ℕ) (b : Fin 2) (hd : 0 < d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent A n d b = 0 := by
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d).ext
  intro u
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_basis, LinearMap.zero_apply]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponentOnWord_eq_zero_of_positive A u.down hd b

/-- 概要：全正次数の語の削除微分の実際の頂点成分は零（BF §2.2.7）。
方針：次数一の二項相殺と、それ以上の頂点線形成分の零性を使う。
規約：削除微分は非全射・退化生成元も元の定義通り含む。
使われ方：余演算の頂点生成元に対する複体射条件。 -/
lemma vertexComponent_differentialOnWord {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) (b : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent A n d b (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differentialOnWord A u) = 0 := by
  cases d with
  | zero => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_differentialOnWord_degree_one A u b
  | succ d =>
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_eq_zero_of_positive A n (d + 1) b (by omega), LinearMap.zero_apply]

/-- 概要：実際の全頂点成分の出力は閉じている（BF §2.2.7）。
方針：次数零では頂点テンソルの微分零、正次数では成分自身の零性を使う。
規約：全 arity・全語次数・両頂点。
使われ方：余演算の頂点生成元の標的微分。 -/
lemma vertexComponentOnWord_d_eq_zero {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (b : Fin 2) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-(d : ℤ)) (-(d : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponentOnWord A u b) = 0 := by
  cases d with
  | zero =>
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponentOnWord, dite_eq_left rfl] using!
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree_d_eq_zero A n 0 (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_tupleDegree n b)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector_d_eq_zero_of_vertices A n (fun _ => b))
  | succ d =>
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponentOnWord_eq_zero_of_positive A u (by omega) b, map_zero]

/-- 概要：正次数の実際の頂点成分は削除微分と可換（BF §2.2.7）。
方針：元の正次数頂点成分と削除微分の頂点成分がともに零であることを使う。
規約：標的次数を実際の削除後次数へ揃える。
使われ方：χ の区間余演算を実際の複体射へ束ねる。 -/
lemma vertexComponentOnWord_d_positive {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) (b : Fin 2) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-((d + 1 : ℕ) : ℤ)) (-(d : ℤ))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponentOnWord A u b) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent A n d b (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differentialOnWord A u) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponentOnWord_eq_zero_of_positive A u (by omega) b, map_zero,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_differentialOnWord A u b]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
