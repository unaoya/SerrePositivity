module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.SupportPairing

/-!
概要：twisted arrow のホーンの重みで固定する部分複体を標準単体内に表示する。
方針：左右の半分と指定番号以外の二頂点を欠く面を和でまとめる。
規約：この領域の包含の inner anodyne 性は、頂点集合の pairing の正則性の後に示す。
使われ方：既存のホーン充填の還元と、有限頂点集合の pairing の接続。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- twisted arrow の n 次の i 番目のホーンで固定する、左右の半分と残りの面の和。 -/
def twistedArrowExtensionDomain (n : ℕ) (i : Fin (n + 1)) :
    (Δ[n + n + 1] : SSet.{u}).Subcomplex :=
  stdSimplex.face ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices n)ᶜ) ⊔
    (stdSimplex.face (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices n) ⊔
      ⨆ j : {j : Fin (n + 1) // j ≠ i},
        stdSimplex.face ({_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n j.val, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n j.val}ᶜ))

/-- 領域への単体の所属は、左右の半分または欠ける一対で判定できる。 -/
lemma mem_twistedArrowExtensionDomain_iff {n d : ℕ} (i : Fin (n + 1))
    (s : (Δ[n + n + 1] : SSet.{u}) _⦋d⦌) :
    s ∈ (twistedArrowExtensionDomain n i).obj (Opposite.op ⦋d⦌) ↔
      (∀ k : Fin (d + 1), (s k).val ≤ n) ∨
      (∀ k : Fin (d + 1), n < (s k).val) ∨
      ∃ j : Fin (n + 1), j ≠ i ∧ ∀ k : Fin (d + 1),
        s k ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n j ∧ s k ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n j := by
  change (s ∈ (stdSimplex.face ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices n)ᶜ)).obj _ ∨
    s ∈ (stdSimplex.face (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices n)).obj _ ∨
    s ∈ (⨆ j : {j : Fin (n + 1) // j ≠ i},
      stdSimplex.face ({_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n j.val, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n j.val}ᶜ)).obj _) ↔ _
  simp only [
    Subfunctor.iSup_obj, Set.mem_iUnion, stdSimplex.mem_face_iff,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
    true_and, not_lt, Finset.mem_insert, Finset.mem_singleton, not_or,
    Subtype.exists, exists_prop]

/-- 領域への所属は、pairing に用いる有限頂点集合の条件そのもの。 -/
lemma mem_twistedArrowExtensionDomain_iff_support {n d : ℕ} (i : Fin (n + 1))
    (s : (Δ[n + n + 1] : SSet.{u}) _⦋d⦌) :
    s ∈ (twistedArrowExtensionDomain n i).obj (Opposite.op ⦋d⦌) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowSupportInDomain i (Finset.univ.image s) := by
  rw [mem_twistedArrowExtensionDomain_iff]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowSupportInDomain, Finset.mem_univ,
    Finset.mem_image, true_and, not_exists]
  constructor
  · rintro (h | h | ⟨j, hj, h⟩)
    · exact Or.inl (fun v hv ↦ by obtain ⟨k, rfl⟩ := hv; exact h k)
    · exact Or.inr (Or.inl (fun v hv ↦ by obtain ⟨k, rfl⟩ := hv; exact h k))
    · exact Or.inr (Or.inr ⟨j, hj, fun k ↦ (h k).1, fun k ↦ (h k).2⟩)
  · rintro (h | h | ⟨j, hj, hl, hr⟩)
    · exact Or.inl (fun k ↦ h (s k) ⟨k, rfl⟩)
    · exact Or.inr (Or.inl (fun k ↦ h (s k) ⟨k, rfl⟩))
    · exact Or.inr (Or.inr ⟨j, hj, fun k ↦ ⟨hl k, hr k⟩⟩)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
