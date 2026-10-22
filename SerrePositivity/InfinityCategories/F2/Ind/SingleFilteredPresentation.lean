module

public import SerrePositivity.InfinityCategories.F2.Ind.FilteredElementsClosure

/-!
概要：Indκ の対象は、元の小さい元の圏上の単一 κ-filtered 表現可能図式の余極限である。
方針：最小閉包と元の right unstraightening 条件の同値を、同じ canonical 密度余錐に適用する。
規約：正則 κ。元の前層頂点を厳密に保ち、反復閉包の存在で表示を代用しない。
使われ方：HTT 5.3.5.4 と、κ-filtered 余極限を保つ延長の構成。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] (C : SSet.{u}) [Quasicategory C]

/-- 一つの小さい κ-filtered 図式からの、指定した前層頂点そのものを持つ表現可能生成表示。 -/
def HasSingleFilteredRepresentablePresentation (v : (PresheafInfinity C) _⦋0⦌) : Prop :=
  ∃ (I : SSet.{u}) (hI : Quasicategory I),
    letI := hI
    IsKappaFiltered κ I ∧
    ∃ a : I ⟶ C, ∃ c : JoinCocone
      ((SSet.uliftFunctor.{u + 1, u}).map a ≫ yonedaInfinityMap C),
      c.vertex = v ∧ IsColimitCone c

/-- 任意の Indκ 頂点は、元の right unstraightening 上の同じ密度余錐による単一表示を持つ。 -/
lemma isIndVertex_has_singleFilteredPresentation {v : (PresheafInfinity C) _⦋0⦌}
    (hv : IsIndVertex κ C v) : HasSingleFilteredRepresentablePresentation κ C v := by
  let F := (presheafInfinityObjectEquiv C).symm v
  have hF : functorVertex F = v := (presheafInfinityObjectEquiv C).apply_symm_apply v
  have hi : IsIndVertex κ C (functorVertex F) := hF.symm ▸ hv
  have hk := (isIndVertex_functorVertex_iff κ C F).mp hi
  refine ⟨smallRightUnstraightening F, inferInstance, hk,
    smallRightUnstraighteningProjection F, presheafDensityCocone F, ?_,
    presheafDensityCocone_isColimit F⟩
  exact (presheafDensityCocone_vertex F).trans hF

/-- 単一の小さい κ-filtered 表現可能表示を持つ前層は、Indκ の最小閉包に属する。 -/
lemma isIndVertex_of_singleFilteredPresentation {v : (PresheafInfinity C) _⦋0⦌}
    (hv : HasSingleFilteredRepresentablePresentation κ C v) : IsIndVertex κ C v := by
  obtain ⟨I, hI, hκ, a, c, hc, hcol⟩ := hv
  have := hI
  have := hκ
  have h := isIndVertex_kappaColimitClosed κ C I
    ((SSet.uliftFunctor.{u + 1, u}).map a ≫ yonedaInfinityMap C) c hcol
    (fun i => isIndVertex_yoneda κ (a.app (Opposite.op ⦋0⦌) i))
  exact hc ▸ h

/-- 最小 κ-filtered 閉包は、単一の小さい κ-filtered 表現可能生成表示の条件と同値。 -/
lemma isIndVertex_iff_singleFilteredPresentation (v : (PresheafInfinity C) _⦋0⦌) :
    IsIndVertex κ C v ↔ HasSingleFilteredRepresentablePresentation κ C v :=
  ⟨isIndVertex_has_singleFilteredPresentation κ C,
    isIndVertex_of_singleFilteredPresentation κ C⟩

end SerrePositivity.InfinityCategories.F2.Ind
