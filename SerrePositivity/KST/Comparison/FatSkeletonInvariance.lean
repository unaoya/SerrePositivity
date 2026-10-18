module

public import SerrePositivity.KST.Comparison.FatAttachmentSpan
public import SerrePositivity.KST.Comparison.FatSkeletonZero
public import SerrePositivity.KST.Comparison.SpanCylinderColimitNaturality
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor

/-!
# 有限骨格の各行の局所化同型に対する不変性

概要：各行で局所化同型である射は全ての有限骨格でも局所化同型を誘導する。
方針：零骨格の同型と、単射な脚の span の余極限の不変性による帰納。
規約：Segal 1974 Proposition 1.6 の各行の Kan 置換からの復元。
使われ方：各行の Kan 性の技術的仮定を取り除く。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：各行の局所化同型は全ての有限骨格で局所化同型を誘導する。
方針：付着の span の三頂点で局所化同型を確認して実際の pushout へ移す。
規約：各行の単射性や Kan 性は不要。
使われ方：関手的 Kan 分解の単位による有限骨格の比較。
-/
theorem fatSkeletonMap_localized_isIso
    {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G)
    (hα : ∀ m, IsIso (AnodyneHomotopy.anodyneQ.map (α.app (op ⦋m⦌)))) :
    ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (fatSkeletonMap α n)) := by
  intro n
  induction n with
  | zero =>
    have h : fatSkeletonRow F 0 ≫ fatSkeletonMap α 0 =
        (α.app (op ⦋0⦌) ▷ Δ[0]) ≫ fatSkeletonRow G 0 := by
      exact fatSkeletonRowOfLE_map α (le_refl 0)
    have hi := AnodyneHomotopy.whiskerRight_anodyneQ_isIso _ (hα 0) Δ[0]
    have hx : IsIso (AnodyneHomotopy.anodyneQ.map (fatSkeletonRow F 0) ≫
        AnodyneHomotopy.anodyneQ.map (fatSkeletonMap α 0)) := by
      rw [← Functor.map_comp, h, Functor.map_comp]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp hx
  | succ n ih =>
    apply spanColimit_map_localized_isIso (fatAttachmentSpanMap α n) ?_
      (fatAttachmentCocone F n) (fatAttachmentCoconeIsColimit F n)
      (fatAttachmentCocone G n) (fatAttachmentCoconeIsColimit G n)
      (fatSkeletonMap α (n + 1)) (fatAttachmentCocone_map α n)
    intro d
    rcases d with (_ | _ | _)
    · exact AnodyneHomotopy.whiskerRight_anodyneQ_isIso _ (hα (n + 1)) _
    · exact ih
    · exact AnodyneHomotopy.whiskerRight_anodyneQ_isIso _ (hα (n + 1)) _

end SerrePositivity.KST.Comparison
