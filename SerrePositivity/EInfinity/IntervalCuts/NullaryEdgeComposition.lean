module

public import SerrePositivity.EInfinity.IntervalCuts.NullaryCutSigns
public import SerrePositivity.EInfinity.IntervalCuts.EdgeGeneratorCutSum

/-!
# 空語合成の実際の辺部分合成則

概要：Berger–Fresse §2.2.6・§3.1 の nullary 辺合成を実際の左右の値として証明する。
方針：唯一の空語分割と非零切断の有限同値で辺成分を二段作用と同じ和へ移す。
規約：外側全語次数、退化する削除語、出力 arity 零を含む。
使われ方：三生成元外延性による全整数複体射の合成則の最後の入力。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：空語の重なる分割は存在すれば一意（BF §1.2.4）。
方針：空語分割は一部分を強制し、一部分割の一意性を使う。
規約：部分数は任意に指定できる。
使われ方：nullary 合成の分割和を一項にする。 -/
lemma overlapPartition_empty_eq {t : ℕ} (r s : OverlapPartition t 0) : r = s := by
  have ht := r.count_eq_one_of_empty
  subst t
  exact r.eq_single.trans s.eq_single.symm

/-- 概要：空語分割が存在すると合成は正規化前の削除語の生成元（BF §1.2.4）。
方針：唯一の空語分割と正符号を評価する。
規約：削除語の非退化性は仮定しない。
使われ方：実際の合成辺成分を任意語生成元の切断和へ移す。 -/
lemma compositionOnWords_nullary_eq_generator {m d : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord 0 0) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) 0) :
    compositionOnWords A u v k = generator A (d := d) (nullaryRawWord u v k r) := by
  let _ : Unique (OverlapPartition (occurrenceCount u.val k) 0) :=
    ⟨⟨r⟩, fun s => overlapPartition_empty_eq s r⟩
  simp only [compositionOnWords, Fintype.sum_unique, compositionSign_inner_degree_zero,
    one_smul, compositeGenerator_nullaryRawWord]
  rw [overlapPartition_empty_eq (default : OverlapPartition (occurrenceCount u.val k) 0) r]

/-- 概要：空語合成の辺成分は二段作用と同じ整数係数・全出力族の和（BF §2.2.6）。
方針：正規化前の生成元の切断和を有限同値で移し、符号と全出力族を照合する。
規約：退化削除語も非零切断型の空性で同時に扱う。
使われ方：nullary の実際の左右の辺評価を結ぶ共通の有限和。 -/
lemma edgeComponent_composition_nullary_action_sum {m d : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord 0 0) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) 0) :
    edgeComponent A (m + 0) (d + 0) (compositionOnWords A u v k) =
      ∑ a : NestedEdgeCut u v k, a.actionCoefficient •
        tensorVectorAt A (m + 0) a.outputFamily (-((d + 0 + 1 : ℕ) : ℤ)) (by
          rw [a.outputFamily_tupleDegree_all]) := by
  rw [compositionOnWords_nullary_eq_generator A u v k r, edgeComponent_generator,
    dite_eq_left (nullaryRawWord_surjective u v k r)]
  let F := fun q : {q : Fin (m + d) // EdgeNondegenerate (nullaryRawWord u v k r) q} =>
    edgeSign (nullaryRawWord u v k r) q.val •
      tensorVectorOfDegree A m (d + 1) (edgeOutput (nullaryRawCutWord u v k r q) q.val)
        (edgeOutput_tupleDegree _ _ q.property)
  change (∑ q, F q) = _
  rw [← (nullaryNestedCutEquiv u v k r).sum_comp F]
  apply Finset.sum_congr rfl
  intro a _
  change edgeSign (nullaryRawWord u v k r) (nullaryNestedCutEquiv u v k r a).val •
    tensorVectorOfDegree A m (d + 1)
      (edgeOutput (nullaryRawCutWord u v k r (nullaryNestedCutEquiv u v k r a))
        (nullaryNestedCutEquiv u v k r a).val) _ = _
  rw [a.nullary_edgeSign r, a.actionCoefficient_vertex a.nullary_eq_none]
  have H := tensorVectorAt_congr A m
    (edgeOutput (nullaryRawCutWord u v k r (nullaryNestedCutEquiv u v k r a))
      (nullaryNestedCutEquiv u v k r a).val) a.outputFamily (-((d + 1 : ℕ) : ℤ))
    (by rw [edgeOutput_tupleDegree _ _ (nullaryNestedCutEquiv u v k r a).property])
    (by
      have hd : tupleDegree m a.outputFamily = d + 1 := by
        simpa only [Nat.add_zero] using a.outputFamily_tupleDegree_all
      exact congrArg (fun t : ℕ => -(t : ℤ)) hd)
    (nullaryNestedCutEquiv_outputFamily u v k r a)
  exact congrArg (fun x => edgeSign u.val a.val.1 • x) H

/-- 概要：空語を内側に持つ実際の辺部分合成則（BF §2.2.6・§3.1）。
方針：指定色一出現なら共通切断和、そうでなければ左右の零性を使う。
規約：全外側語次数と出力 arity 零。
使われ方：全 arity の複体射の合成則の辺生成元条件。 -/
lemma cochainAction_composition_basis_edge_nullary_eq_iterated {m d : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord 0 0) (i : Fin (m + 1)) :
    ((complexPartialComposition A m 0 i ▷ interval A) ≫ cochainAction A (m + 0)).f
      (-((d + 0 + 1 : ℕ) : ℤ)) (wordPairEdgeInput A u v) =
        (iteratedCochainAction A m 0 i).f (-((d + 0 + 1 : ℕ) : ℤ))
          (wordPairEdgeInput A u v) := by
  by_cases hi : occurrenceCount u.val i = 1
  · let r : OverlapPartition (occurrenceCount u.val i) 0 :=
      cast (congrArg (fun t => OverlapPartition t 0) hi.symm) (OverlapPartition.single 0)
    refine (cochainAction_composition_basis_edge A u v i).trans ?_
    rw [edgeComponent_composition_nullary_action_sum A u v i r]
    have H := iteratedCochainAction_basis_edge_nested_sum A u v i
      (-((d + 0 + 1 : ℕ) : ℤ)) (by omega)
    have hx := SerrePositivity.DifferentialGraded.nested_left_apply
      (complex A (m + 1)) (complex A 0) (interval A) (-(d : ℤ)) (-(0 : ℤ)) (-1)
      (-((d + 0 : ℕ) : ℤ)) (-((d + 0 + 1 : ℕ) : ℤ)) (by omega) (by omega)
      ((complexXIso A (m + 1) d).inv (basis A (m + 1) d (ULift.up u)))
      ((complexXIso A 0 0).inv (basis A 0 0 (ULift.up v))) (faceVector A edge)
    exact H.symm.trans (congrArg (fun x => (iteratedCochainAction A m 0 i).f
      (-((d + 0 + 1 : ℕ) : ℤ)) x) hx).symm
  · exact cochainAction_composition_basis_edge_nullary_eq_iterated_of_count_ne_one A u v i hi

end SerrePositivity.EInfinity.IntervalCuts
