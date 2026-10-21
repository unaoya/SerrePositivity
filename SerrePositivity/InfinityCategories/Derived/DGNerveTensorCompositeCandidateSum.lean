module
public import SerrePositivity.InfinityCategories.Derived.DGNerveCutVertexReindex
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorContributionsSum
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorCandidate
/-!
概要：合成の残存和を同じ左右候補の符号付き合成の和へ同定する。
方針：同じ頂点ごとの切断集合を実添字同値で移し、線形性を使う。
規約：元の全次数の cochain を使う。使われ方：候補自身の全 HA 右辺の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped BigOperators
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 元の残存和と候補の境界成分の比較。 -/
def dgNerveTensorCandidateCompositionTerm {n : ℕ} (s : SimplexData R B n)
    (t : SimplexData R C n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (j : (I.filter (fun x => a < x ∧ x < b))) :
    GradedHom R (D := DGTensorCategory R B C) (s.obj a, t.obj a) (s.obj b, t.obj b) (k + 1) := by
  have hjI := Finset.mem_filter.mp j.property
  let P := I.filter (· ≤ j.val)
  let Q := I.filter (j.val ≤ ·)
  have hP : 2 ≤ P.card := Index.left_two ha.1 hjI.1 hjI.2.1
  have hQ : 2 ≤ Q.card := Index.right_two hjI.1 hb.1 hjI.2.2
  have haP : IsLeast (P : Set (Fin (n + 1))) a :=
    ⟨Finset.mem_filter.mpr ⟨ha.1, hjI.2.1.le⟩,
      fun _ hx => ha.2 (Finset.mem_filter.mp hx).1⟩
  have hjP : IsGreatest (P : Set (Fin (n + 1))) j.val :=
    ⟨Finset.mem_filter.mpr ⟨hjI.1, le_rfl⟩, fun _ hx => (Finset.mem_filter.mp hx).2⟩
  have hjQ : IsLeast (Q : Set (Fin (n + 1))) j.val :=
    ⟨Finset.mem_filter.mpr ⟨hjI.1, le_rfl⟩, fun _ hx => (Finset.mem_filter.mp hx).2⟩
  have hbQ : IsGreatest (Q : Set (Fin (n + 1))) b :=
    ⟨Finset.mem_filter.mpr ⟨hb.1, hjI.2.2.le⟩,
      fun _ hx => hb.2 (Finset.mem_filter.mp hx).1⟩
  exact ((I.filter (j.val < ·)).card : ℤ).negOnePow • compose R (n := k + 1)
    (dgNerveTensorHomCandidate R B C s t Q j.val b (2 - (Q.card : ℤ)) rfl hQ hjQ hbQ)
    (dgNerveTensorHomCandidate R B C s t P a j.val (2 - (P.card : ℤ)) rfl hP haP hjP)
    (by have hcard := Index.split_card hjI.1; dsimp only [P, Q]; omega)
/-- 元の残存和と候補の境界成分の比較。 -/
lemma dgNerveTensorSelectedCompositeSummand_vertex_sum {n : ℕ} (s : SimplexData R B n)
    (t : SimplexData R C n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (j : (I.filter (fun x => a < x ∧ x < b))) :
    (∑ S : DGNerveSelectedCutSubsets (I.filter (fun x => a < x ∧ x < b)) j.val,
      dgNerveTensorSelectedCompositeSummand R B C s t I (I.filter (fun x => a < x ∧ x < b))
        a b k hk ha hb (fun _ hx => Finset.mem_filter.mp hx)
        ((dgNerveCutDeletionVertexEquiv _).symm ⟨j, S⟩)) =
      dgNerveTensorCandidateCompositionTerm R B C s t I a b k hk ha hb j := by
  have hjI := Finset.mem_filter.mp j.property
  let P := I.filter (· ≤ j.val)
  let Q := I.filter (j.val ≤ ·)
  have hP : 2 ≤ P.card := Index.left_two ha.1 hjI.1 hjI.2.1
  have hQ : 2 ≤ Q.card := Index.right_two hjI.1 hb.1 hjI.2.2
  have haP : IsLeast (P : Set (Fin (n + 1))) a :=
    ⟨Finset.mem_filter.mpr ⟨ha.1, hjI.2.1.le⟩,
      fun _ hx => ha.2 (Finset.mem_filter.mp hx).1⟩
  have hjP : IsGreatest (P : Set (Fin (n + 1))) j.val :=
    ⟨Finset.mem_filter.mpr ⟨hjI.1, le_rfl⟩, fun _ hx => (Finset.mem_filter.mp hx).2⟩
  have hjQ : IsLeast (Q : Set (Fin (n + 1))) j.val :=
    ⟨Finset.mem_filter.mpr ⟨hjI.1, le_rfl⟩, fun _ hx => (Finset.mem_filter.mp hx).2⟩
  have hbQ : IsGreatest (Q : Set (Fin (n + 1))) b :=
    ⟨Finset.mem_filter.mpr ⟨hb.1, hjI.2.2.le⟩,
      fun _ hx => hb.2 (Finset.mem_filter.mp hx).1⟩
  let T := I.filter (fun x => a < x ∧ x < b)
  let PL := P.filter (fun x => a < x ∧ x < j.val)
  let QR := Q.filter (fun x => j.val < x ∧ x < b)
  have heL : PL = T.filter (· < j.val) := by
    ext x
    simp only [PL, P, T, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hxI, _⟩, hax, hxj⟩
      exact ⟨⟨hxI, hax, lt_trans hxj hjI.2.2⟩, hxj⟩
    · rintro ⟨⟨hxI, hax, _⟩, hxj⟩
      exact ⟨⟨hxI, hxj.le⟩, hax, hxj⟩
  have heR : QR = T.filter (j.val < ·) := by
    ext x
    simp only [QR, Q, T, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hxI, _⟩, hjx, hxb⟩
      exact ⟨⟨hxI, lt_trans hjI.2.1 hjx, hxb⟩, hjx⟩
    · rintro ⟨⟨hxI, _, hxb⟩, hjx⟩
      exact ⟨⟨hxI, hjx.le⟩, hjx, hxb⟩
  let eL : DGNerveSideCutSubsets T (· < j.val) ≃ PL.powerset :=
    { toFun := fun L => ⟨L.val, Finset.mem_powerset.mpr (by rw [heL]; exact L.property)⟩
      invFun := fun L => ⟨L.val, by rw [← heL]; exact Finset.mem_powerset.mp L.property⟩
      left_inv := fun L => by apply Subtype.ext; rfl
      right_inv := fun L => by apply Subtype.ext; rfl }
  let eR : DGNerveSideCutSubsets T (j.val < ·) ≃ QR.powerset :=
    { toFun := fun L => ⟨L.val, Finset.mem_powerset.mpr (by rw [heR]; exact L.property)⟩
      invFun := fun L => ⟨L.val, by rw [← heR]; exact Finset.mem_powerset.mp L.property⟩
      left_inv := fun L => by apply Subtype.ext; rfl
      right_inv := fun L => by apply Subtype.ext; rfl }
  let e := (dgNerveCutSplitEquiv T j.val j.property).trans (Equiv.prodCongr eL eR)
  let fL := fun L : PL.powerset =>
    dgNerveTensorCutTerm R B C s t P a j.val L.val (2 - (P.card : ℤ)) rfl hP haP hjP
      (fun x hx => Finset.mem_filter.mp (Finset.mem_powerset.mp L.property hx))
  let fR := fun U : QR.powerset =>
    dgNerveTensorCutTerm R B C s t Q j.val b U.val (2 - (Q.card : ℤ)) rfl hQ hjQ hbQ
      (fun x hx => Finset.mem_filter.mp (Finset.mem_powerset.mp U.property hx))
  have hcomp : (2 - (P.card : ℤ)) + (2 - (Q.card : ℤ)) = k + 1 := by
    have hcard := Index.split_card hjI.1
    dsimp only [P, Q]
    omega
  let F := fun L U => ((I.filter (j.val < ·)).card : ℤ).negOnePow •
    compose R (fR U) (fL L) hcomp
  change (∑ S, F (e S).1 (e S).2) =
    ((I.filter (j.val < ·)).card : ℤ).negOnePow •
      compose R (∑ U, fR U) (∑ L, fL L) hcomp
  calc
    _ = ∑ P : PL.powerset × QR.powerset, F P.1 P.2 :=
      Equiv.sum_comp e (fun P => F P.1 P.2)
    _ = ∑ L, ∑ U, F L U := Fintype.sum_prod_type _
    _ = _ := by
      rw [compose_sum_right, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro L _
      rw [compose_sum_left, Finset.smul_sum]
/-- 元の残存和と候補の境界成分の比較。 -/
lemma dgNerveTensorSelectedCompositeSummand_sum {n : ℕ} (s : SimplexData R B n)
    (t : SimplexData R C n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
 :
    (∑ p : DGNerveCutDeletionIndex (I.filter (fun x => a < x ∧ x < b)),
      dgNerveTensorSelectedCompositeSummand R B C s t I (I.filter (fun x => a < x ∧ x < b))
        a b k hk ha hb (fun _ hx => Finset.mem_filter.mp hx) p) =
      ∑ j : (I.filter (fun x => a < x ∧ x < b)),
        dgNerveTensorCandidateCompositionTerm R B C s t I a b k hk ha hb j := by
  rw [dgNerveCutDeletionVertex_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact dgNerveTensorSelectedCompositeSummand_vertex_sum R B C s t I a b k hk ha hb j
end SerrePositivity.InfinityCategories
