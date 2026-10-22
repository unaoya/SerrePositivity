module

public import SerrePositivity.InfinityCategories.F2.Compact.IndComplete
public import SerrePositivity.InfinityCategories.F2.Compact.IdemPresheafCompact
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompleteImageRetracts

/-!
概要：元の前層内の Yoneda retract 閉包 Idem(C) を、元の同じ Indκ(C) へ含める。
方針：Ind の coherent 冪等完備性で元の retract を回収し、同型閉性で元の頂点に戻す。
規約：元の前層包含を厳密に保持。単一 filtered 表示や本質全射性は仮定しない。
使われ方：compact Ind 対象と元の冪等完備化との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {C : SSet.{u}} [Quasicategory C]

/-- 元の前層内の Yoneda retract は、元の同じ Indκ の頂点条件を満たす。 -/
lemma idemPresheaf_isIndVertex (κ : Cardinal.{u}) (F : Idempotent.Idem C _⦋0⦌) :
    Ind.IsIndVertex κ C ((Idempotent.idemInclusionPresheaf C).app _ F) := by
  obtain ⟨x, hx⟩ := Idempotent.idemVertex_retract_yoneda F
  let y := (Ind.indYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up x)
  have hy : (Ind.indInclusionPresheaf κ C).app (Opposite.op ⦋0⦌) y =
      (yonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up x) :=
    congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (ULift.up x)) (Ind.indYoneda_inclusion κ C)
  rw [← hy] at hx
  obtain ⟨z, ⟨e⟩⟩ := (ind_isIdempotentComplete κ C).retract_iso_in_image
    (Ind.indInclusionPresheaf κ C) (Ind.indInclusionPresheaf_isFullyFaithful κ C)
    y ((Idempotent.idemInclusionPresheaf C).app _ F) hx.some
  exact Ind.isIndVertex_isoClosed κ C e.symm (fullSubcomplexOnVertices_vertex z)

/-- 元の Idem(C) の全図式を、同じ前層内の元の Indκ(C) へ因子化する。 -/
def idemToInd (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] :
    Idempotent.Idem C ⟶ Ind.IndInfinity κ C :=
  fullSubcomplexLift (Ind.IsIndVertex κ C) (Idempotent.idemInclusionPresheaf C)
    (idemPresheaf_isIndVertex κ)

/-- 元の前層への全包含を、同じ実写像として厳密に保持する。 -/
lemma idemToInd_inclusion (κ : Cardinal.{u}) :
    idemToInd κ C ≫ Ind.indInclusionPresheaf κ C = Idempotent.idemInclusionPresheaf C :=
  fullSubcomplexLift_ι _ _ _

/-- 元の Idem(C) から Indκ(C) への同じ実写像は充満忠実。 -/
lemma idemToInd_isFullyFaithful (κ : Cardinal.{u}) : IsFullyFaithful (idemToInd κ C) := by
  apply (Ind.indInclusionPresheaf_isFullyFaithful κ C).cancel_right
  rw [idemToInd_inclusion]
  exact Idempotent.idemInclusionPresheaf_isFullyFaithful C

/-- 元の Idem(C) の同じ実像は、元の Indκ 内で κ-compact。 -/
lemma idemToInd_isKappaCompact (κ : Cardinal.{u}) (F : Idempotent.Idem C _⦋0⦌) :
    IsKappaCompact.{u, u + 1} κ ((idemToInd κ C).app _ F) := by
  apply ind_isKappaCompact_of_presheaf
  change IsKappaCompact.{u, u + 1} κ
    ((idemToInd κ C ≫ Ind.indInclusionPresheaf κ C).app _ F)
  rw [idemToInd_inclusion]
  exact idemPresheaf_isKappaCompact κ F

end SerrePositivity.InfinityCategories.F2.Compact
