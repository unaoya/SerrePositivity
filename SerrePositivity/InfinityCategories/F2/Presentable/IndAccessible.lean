module

public import SerrePositivity.InfinityCategories.F2.Presentable.Accessible
public import SerrePositivity.InfinityCategories.F2.Ind.SingleFilteredPresentation
public import SerrePositivity.InfinityCategories.F2.Compact.IndCompact
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentCoconeTransport

/-!
概要：正則 κ について、小さい ∞ 圏の Indκ は κ-accessible である。
方針：既存の単一表示の全余錐を持ち上げ、Yoneda 像の κ-compact 性と合わせる。
規約：元の頂点・全図式を保持。Ind との同値を accessibility の定義に入れない。
使われ方：HTT 5.4.2 の Ind 表現の一方向。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open Ind HomotopyLimits
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] (A : SSet.{u}) [Quasicategory A]

/-- 元の Ind 頂点そのものを持つ、同じ小さい生成圏からの単一 filtered 表示。 -/
lemma indYoneda_generatorPresentation (x : IndInfinity κ A _⦋0⦌) :
    HasKappaFilteredGeneratorPresentation κ (indYoneda κ A) x := by
  have hx := fullSubcomplexOnVertices_vertex x
  obtain ⟨I, hI, hκ, a, c, hc, hcol⟩ :=
    isIndVertex_has_singleFilteredPresentation κ A hx
  let D := (SSet.uliftFunctor.{u + 1, u}).map a ≫ indYoneda κ A
  have hD : D ≫ indInclusionPresheaf κ A =
      (SSet.uliftFunctor.{u + 1, u}).map a ≫ yonedaInfinityMap A := by
    rw [Category.assoc, indYoneda_inclusion]
  let d := coherentCoconeOfDiagramEq hD.symm c
  have hd : IsIndVertex κ A d.vertex := by
    rw [coherentCoconeOfDiagramEq_vertex, hc]
    exact hx
  refine ⟨I, hI, hκ, a, fullCoconeLift (IsIndVertex κ A) D d hd, ?_, ?_⟩
  · apply Subtype.ext
    have h := congrArg JoinCocone.vertex (fullCoconeLift_inclusion (IsIndVertex κ A) D d hd)
    exact h.trans ((coherentCoconeOfDiagramEq_vertex _ _).trans hc)
  · apply fullCoconeLift_isColimit
    exact (coherentCoconeOfDiagramEq_isColimit_iff _ _).mp hcol

/-- 元の Yoneda 自身が、Indκ の小さい κ-compact な全部分生成圏を与える。 -/
lemma indYoneda_isKappaCompactGenerating :
    IsKappaCompactGenerating κ (indYoneda κ A) where
  fullyFaithful := indYoneda_isFullyFaithful κ A
  compact := Compact.indYoneda_isKappaCompact κ
  presentation := indYoneda_generatorPresentation κ A

/-- Indκ は、小さい κ-filtered 余極限と κ-compact 生成による意味で κ-accessible。 -/
lemma indInfinity_isKappaAccessible : IsKappaAccessible κ (IndInfinity κ A) :=
  ⟨Fact.out, ind_hasSmallKappaFilteredColimits κ A,
    A, inferInstance, indYoneda κ A, indYoneda_isKappaCompactGenerating κ A⟩

lemma indInfinity_isAccessible : IsAccessible (IndInfinity κ A) :=
  (indInfinity_isKappaAccessible κ A).isAccessible

end SerrePositivity.InfinityCategories.F2.Presentable
