module

public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafYonedaLeftKan
public import SerrePositivity.InfinityCategories.F2.Ind.IndContinuousLeftKan

/-!
概要：余完備な Ind 模型への前層左 Kan 延長を包含へ制限し、密度余錐を回収する。
方針：元の elements 比較と密度余錐の包含公式で全写像を照合する。
規約：Ind 側の公開 API だけを使い、余完備性は明示する。
使われ方：反映の単位・余単位と三角恒等式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]

/-- 概要：Ind の標準余錐の像の普遍性は元の密度余錐の像で判定できる。
方針：公開された elements 比較と元の全写像の一致を使う。
規約：同じ元の関手を判定する。
使われ方：前層反映の制限の密度保存。 -/
lemma indReflectorCanonicalColimits_iff_densityImages {D : SSet.{u + 1}}
    [Quasicategory D] (G : IndInfinity κ C ⟶ D) :
    (∀ v, IsColimitCone (leftKanCanonicalCocone (indYoneda κ C) G v)) ↔
      ∀ v, IsColimitCone (mapJoinCocone G (indVertexDensityCocone κ v)) := by
  have h (v : (IndInfinity κ C) _⦋0⦌) :=
    (isColimitCone_iff_restrict_equivalentShape (indElementsLeftKanComparison κ v)
      (indElementsLeftKanComparison_isQCatEquivalence κ v)
      (leftKanCanonicalCocone (indYoneda κ C) G v)).trans
      (F2.isColimitCone_iff_of_cocone_val_eq _ _
        (indLeftKanCanonicalCocone_restrict_val κ G v))
  exact ⟨fun hc v ↦ (h v).mp (hc v), fun hc v ↦ (h v).mpr (hc v)⟩

/-- 概要：Ind の密度余錐を前層へ包含すると元の前層密度余錐と一致する。
方針：元の前層を回収した頂点の公開包含公式を使う。
規約：全余錐の値としての厳密な一致。
使われ方：反映前後の密度の照合。 -/
lemma indReflectorVertexDensityCocone_val_inclusion (v : (IndInfinity κ C) _⦋0⦌) :
    (indVertexDensityCocone κ v).val ≫ indInclusionPresheaf κ C =
      (presheafDensityCocone (indVertexPresheaf κ v)).val := by
  exact congrArg Subtype.val
    (indDensityCocone_inclusion κ (indVertexPresheaf κ v) (indVertexPresheaf_mem κ v))

/-- 概要：Ind の恒等関手の全標準余錐は余極限。
方針：元の密度余錐の普遍性を標準余錐へ戻す。
規約：同じ恒等関手を使用する。
使われ方：余単位の可逆性の検出。 -/
lemma indReflectorIdentity_canonicalColimits (v : (IndInfinity κ C) _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone (indYoneda κ C) (𝟙 _) v) := by
  apply (indReflectorCanonicalColimits_iff_densityImages (𝟙 (IndInfinity κ C))).mpr
    (fun w ↦ ?_) v
  exact (F2.isColimitCone_iff_of_cocone_val_eq (indVertexDensityCocone κ w)
    (mapJoinCocone (𝟙 _) (indVertexDensityCocone κ w)) (by simp [mapJoinCocone])).mp
      (indVertexDensityCocone_isColimit κ w)

variable {L : PresheafInfinity C ⟶ IndInfinity κ C}
    (β : SSet.Homotopy (indYoneda κ C) (yonedaInfinityMap C ≫ L))
    (hβ : IsLeftKanExtension (yonedaInfinityMap C) (indYoneda κ C) L β)
include β hβ

/-- 概要：前層左 Kan 候補の Ind 上の制限は全標準密度余錐を保つ。
方針：前層密度余錐の像の余極限性を包含の全写像の一致で戻す。
規約：包含が全小余極限を保存するとは仮定しない。
使われ方：反映の余単位の構成。 -/
lemma indReflectorRestriction_canonicalColimits (v : (IndInfinity κ C) _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone (indYoneda κ C)
      (indInclusionPresheaf κ C ≫ L) v) := by
  apply (indReflectorCanonicalColimits_iff_densityImages (indInclusionPresheaf κ C ≫ L)).mpr
    (fun w ↦ ?_) v
  apply (F2.isColimitCone_iff_of_cocone_val_eq
    (mapJoinCocone L (presheafDensityCocone (indVertexPresheaf κ w)))
    (mapJoinCocone (indInclusionPresheaf κ C ≫ L) (indVertexDensityCocone κ w)) ?_).mp
      (presheafYonedaLeftKan_density_image_isColimit β hβ _)
  change _ ≫ L = _ ≫ (_ ≫ L)
  rw [← Category.assoc, indReflectorVertexDensityCocone_val_inclusion]

end SerrePositivity.InfinityCategories.F2.Presentable
