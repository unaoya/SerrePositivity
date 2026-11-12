module

public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.Order.CompleteLattice.Finset

/-!
概要：指定面を含まない面の合併と、指定頂点で欠ける面の境界を構成する。
方針：元の標準単体内の面の合併を使い、面の包含関係を頂点集合の包含へ戻す。
規約：全単体を保持し、非退化単体の集合だけを部分複体とは扱わない。
使われ方：HTT 4.4.5.8 の内角ホーンによる有限貼付け。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 指定した頂点集合の面を含まない面全体の合併。 -/
def missingFaceComplex {n : ℕ} (J : Finset (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subcomplex :=
  ⨆ i ∈ J, stdSimplex.face {i}ᶜ

/-- 元の部分複体への所属は、元の単体の頂点像が指定面を含まないことと同値。 -/
lemma mem_missingFaceComplex {n m : ℕ} (J : Finset (Fin (n + 1)))
    (a : (Δ[n] : SSet.{u}) _⦋m⦌) :
    a ∈ (missingFaceComplex J).obj (Opposite.op ⦋m⦌) ↔
      ¬J ⊆ Finset.univ.image (fun v : Fin (m + 1) ↦ a v) := by
  simp only [missingFaceComplex, Subfunctor.iSup_obj, Set.mem_iUnion,
    stdSimplex.mem_face_iff, Finset.mem_compl, Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj, ha⟩ hJ
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp (hJ hj)
    exact ha v hv
  · intro hJ
    obtain ⟨j, hj, ha⟩ := Finset.not_subset.mp hJ
    refine ⟨j, hj, ?_⟩
    intro v hv
    exact ha (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩)

/-- 指定した面の境界から、指定した一頂点を欠く面だけを除いた合併。 -/
def puncturedFace {n : ℕ} (S : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    (Δ[n] : SSet.{u}).Subcomplex :=
  ⨆ i ∈ S, ⨆ (_ : i ≠ j), stdSimplex.face (S.erase i)

/-- 既に貼った元の面の有限族を、元の指定面を避ける部分複体へ加えた段階。 -/
def missingFaceStage {n : ℕ} (J : Finset (Fin (n + 1)))
    (F : Finset (Finset (Fin (n + 1)))) : (Δ[n] : SSet.{u}).Subcomplex :=
  missingFaceComplex J ⊔ ⨆ T ∈ F, stdSimplex.face T

/-- 元の指定面を避ける部分複体は全ての元の貼付け段階に含まれる。 -/
lemma missingFaceComplex_le_stage {n : ℕ} (J : Finset (Fin (n + 1)))
    (F : Finset (Finset (Fin (n + 1)))) :
    missingFaceComplex.{u} J ≤ missingFaceStage J F := le_sup_left

/-- 元の面を一つ加える段階は、同じ元の面との合併。 -/
lemma missingFaceStage_insert {n : ℕ} (J S : Finset (Fin (n + 1)))
    (F : Finset (Finset (Fin (n + 1)))) :
    missingFaceStage.{u} J (insert S F) = missingFaceStage J F ⊔ stdSimplex.face S := by
  simp only [missingFaceStage, Finset.iSup_insert]
  ac_rfl

/-- 頂点を一つ除いた元の面は、同じ頂点を除く全余次元一面に含まれる。 -/
lemma face_erase_le_complement {n : ℕ} (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    stdSimplex.face.{u} (S.erase i) ≤ stdSimplex.face {i}ᶜ := by
  apply (stdSimplex.face_le_face_iff _ _).mpr
  intro a ha
  simpa only [Finset.mem_compl, Finset.mem_singleton] using (Finset.mem_erase.mp ha).1

/-- 元の欠けた面の合併は、元の面全体に含まれる。 -/
lemma puncturedFace_le_face {n : ℕ} (S : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    puncturedFace.{u} S j ≤ stdSimplex.face S := by
  apply iSup_le
  intro i
  apply iSup_le
  intro hi
  apply iSup_le
  intro hij
  exact (stdSimplex.face_le_face_iff _ _).mpr (Finset.erase_subset _ _)

/-- 内点を除く全頂点集合を使うと、元の全単体の同じ内角ホーンを回収する。 -/
lemma missingFaceComplex_complement {n : ℕ} (j : Fin (n + 1)) :
    missingFaceComplex.{u} {j}ᶜ = horn n j := by
  rw [missingFaceComplex, horn_eq_iSup]
  apply le_antisymm
  · apply iSup_le
    intro i
    apply iSup_le
    intro hi
    have hij : i ≠ j := by simpa using hi
    exact le_iSup_of_le ⟨i, hij⟩ le_rfl
  · apply iSup_le
    intro (i : ({j}ᶜ : Set (Fin (n + 1))))
    have hi : i.val ∈ ({j}ᶜ : Finset (Fin (n + 1))) := by
      simpa only [Finset.mem_compl, Finset.mem_singleton, Set.mem_compl_iff,
        Set.mem_singleton_iff] using i.property
    exact le_iSup_of_le i.val (le_iSup_of_le hi le_rfl)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
