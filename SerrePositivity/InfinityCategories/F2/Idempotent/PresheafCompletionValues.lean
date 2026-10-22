module

public import SerrePositivity.InfinityCategories.F2.Idempotent.UniverseRetracts
public import SerrePositivity.InfinityCategories.F2.Idempotent.PresheafKanExtension
public import SerrePositivity.InfinityCategories.F2.Idempotent.Completion

/-!
概要：冪等完備化上へ実際に構成した前層値の延長は、元の Yoneda retract 閉包に値を持つ。
方針：元の対象の retract を持ち上げて全関手で写し、元の厳密な制限を使う。
規約：各値の表現可能性を入力に仮定せず、元の完成の条件から導く。
使われ方：HTT 5.1.4.8 の前層を介する延長の存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の Yoneda 後合成を厳密に延長した関手の全値は、元の Yoneda 像の retract。 -/
lemma presheafCompletionExtension_values {K C E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory E]
    (δ : K ⟶ C) (hδ : IsIdempotentCompletion δ) (F : K ⟶ E)
    (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ PresheafInfinity E)
    (hG : (SSet.uliftFunctor.{u + 1, u}).map δ ≫ G =
      (SSet.uliftFunctor.{u + 1, u}).map F ≫ yonedaInfinityMap E)
    (c : ((SSet.uliftFunctor.{u + 1, u}).obj C) _⦋0⦌) :
    IsRetractPresheaf (G.app (Opposite.op ⦋0⦌) c) := by
  obtain ⟨c⟩ := c
  obtain ⟨k, hck⟩ := hδ.2.2 c
  have hk := hck.ulift.map G
  have he := congrArg
    (fun H : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ PresheafInfinity E ↦
      H.app (Opposite.op ⦋0⦌) (ULift.up k)) hG
  have hm : IsRetractPresheaf
      (G.app (Opposite.op ⦋0⦌) (ULift.up (δ.app (Opposite.op ⦋0⦌) k))) :=
    he.symm ▸ (mem_retractClosure ⟨F.app (Opposite.op ⦋0⦌) k, rfl⟩)
  exact isRetractPresheaf_of_retract hk hm

/-- 元の Yoneda 後合成の厳密な前層延長を構成し、全値の retract 条件も実際に証明する。 -/
lemma exists_presheafCompletion_extension {K C E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory E]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsIdempotentCompletion δ)
    (F : K ⟶ E) :
    ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ PresheafInfinity E,
      ((SSet.uliftFunctor.{u + 1, u}).map δ ≫ G =
        (SSet.uliftFunctor.{u + 1, u}).map F ≫ yonedaInfinityMap E) ∧
      ∀ c, IsRetractPresheaf (G.app (Opposite.op ⦋0⦌) c) := by
  obtain ⟨G, hG, _hcol⟩ := exists_presheafKan_strict_extension δ hδ.2.1
    ((SSet.uliftFunctor.{u + 1, u}).map F ≫ yonedaInfinityMap E)
  exact ⟨G, hG, presheafCompletionExtension_values δ hδ F G hG⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
