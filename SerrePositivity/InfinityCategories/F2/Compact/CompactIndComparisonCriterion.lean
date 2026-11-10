module

public import SerrePositivity.InfinityCategories.F2.Compact.CompactIndComparison
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful

/-!
概要：元の Idem(C) と compact Ind 対象の比較を、元の Yoneda retract の回収へ還元する。
方針：元の比較の充満忠実性・元の Idem の coherent 完備性・同じ retract を使う。
規約：retract の回収自体はここで仮定として明示し、単一 filtered 表示を証明したと扱わない。
使われ方：F1 の単一表示と compact 性による恒等射の因子化から、全 ∞ 圏同値へ接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
open Idempotent
variable {C : SSet.{u}} [Quasicategory C]

/-- 元の比較の各像は、同じ compact Ind 内で元の compact Yoneda 像の retract。 -/
lemma idemToCompactInd_retract_yoneda (κ : Cardinal.{u}) (F : Idem C _⦋0⦌) :
    ∃ x : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf ((idemToCompactInd κ C).app _ F)
      ((compactIndYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up x)) := by
  obtain ⟨x, hx⟩ := idemVertex_retract_idemYoneda F
  have h := hx.map (idemToCompactInd κ C)
  have he := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (ULift.up x))
    (idemYoneda_toCompactInd (C := C) κ)
  exact ⟨x, he ▸ h⟩

/-- 同じ元の比較の本質全射性は、同じ compact Ind 内の Yoneda retract 条件と同値。 -/
lemma idemToCompactInd_isEssentiallySurjective_iff_retracts (κ : Cardinal.{u}) :
    IsEssentiallySurjective (idemToCompactInd κ C) ↔
      ∀ y : kappaCompactObjects.{u, u + 1} κ (Ind.IndInfinity κ C) _⦋0⦌,
        ∃ x : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf y
          ((compactIndYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up x)) := by
  constructor
  · intro h y
    obtain ⟨F, ⟨e⟩⟩ := h y
    obtain ⟨x, hx⟩ := idemToCompactInd_retract_yoneda κ F
    exact ⟨x, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.of_iso e.symm).trans hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y
    let a := (idemYoneda C).app (Opposite.op ⦋0⦌) (ULift.up x)
    have he : (idemToCompactInd κ C).app (Opposite.op ⦋0⦌) a =
        (compactIndYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up x) :=
      congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (ULift.up x))
        (idemYoneda_toCompactInd (C := C) κ)
    rw [← he] at hx
    obtain ⟨F, ⟨e⟩⟩ := (idem_isIdempotentComplete C).retract_iso_in_image
      (idemToCompactInd κ C) (idemToCompactInd_isFullyFaithful κ) a y hx.some
    exact ⟨F, ⟨e.symm⟩⟩

/-- 元の compact Ind 対象の Yoneda retract 回収から、同じ実比較自身の全 ∞ 圏同値を得る。 -/
lemma idemToCompactInd_isQCatEquivalence_of_retracts (κ : Cardinal.{u})
    (h : ∀ y : kappaCompactObjects.{u, u + 1} κ (Ind.IndInfinity κ C) _⦋0⦌,
      ∃ x : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf y
        ((compactIndYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up x))) :
    IsQCatEquivalence (idemToCompactInd κ C) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (idemToCompactInd_isFullyFaithful κ)
    ((idemToCompactInd_isEssentiallySurjective_iff_retracts κ).mpr h)

end SerrePositivity.InfinityCategories.F2.Compact
