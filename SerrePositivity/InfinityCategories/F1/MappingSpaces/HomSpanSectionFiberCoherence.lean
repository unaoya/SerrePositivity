module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorIsoEndpointProjection
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.HomSpanSectionUnitCoherence
public import SerrePositivity.InfinityCategories.F1.Fibrations.TrivialKanFunctorIsoProjection
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorIsoPrecompositionCoherence
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerComposition

/-!
概要：元の fiber 内比較は、同じ指定切断の単位比較を前合成したもの。
方針：両者の射影が同じ等号同型を回収することを充満忠実性で反映する。
規約：fiber 内で選ばれた比較同型と既存の単位同型の値を保持する。
使われ方：大域の元の分類 Hom 自然性と共有頂点での輸送三角形を結ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の切断の単位を指定した共通始域に戻し、端点だけを正規化する。 -/
def homSpanSectionSourcePrecompIso {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) (s : B ⟶ E)
    (hp : IsFullyFaithful p) (hs : s ≫ p = 𝟙 B) (r n : A ⟶ E)
    (hn : n = (r ≫ p) ≫ s) : FunctorIso n r :=
  F2.functorIsoOfEq ((homSpanSectionSourceIso p s hp hs).precomp r)
    ((Category.assoc r p s).symm.trans hn.symm) (Category.comp_id r)

/-- 同じ共通始域での切断の単位は、射影後に元の持ち上げの等式へ戻る。 -/
lemma homSpanSectionSourcePrecompIso_projection {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) (s : B ⟶ E)
    (hp : IsFullyFaithful p) (hs : s ≫ p = 𝟙 B) (r n : A ⟶ E)
    (hn : n = (r ≫ p) ≫ s) (h : n ≫ p = r ≫ p) :
    (homSpanSectionSourcePrecompIso p s hp hs r n hn).postcomp p =
      eqToIso (congrArg
        (fun v : A ⟶ B ↦ SSet.HomotopyCategory.mk (functorVertex v)) h) := by
  have h₀ : (p ≫ s) ≫ p = 𝟙 E ≫ p := by
    simp only [Category.assoc, hs, Category.comp_id, Category.id_comp]
  have h₁ : (r ≫ (p ≫ s)) ≫ p = (r ≫ 𝟙 E) ≫ p := by
    simp only [Category.assoc, hs, Category.comp_id]
  have he : (((homSpanSectionSourceIso p s hp hs).precomp r).postcomp p) =
      eqToIso (congrArg
        (fun v : A ⟶ B ↦ SSet.HomotopyCategory.mk (functorVertex v)) h₁) := by
    rw [F2.functorIso_precomp_postcomp, homSpanSectionSourceIso_projection,
      FunctorIso.precomp_eqToIso]
    exact h₀
  exact functorIsoOfEq_postcomp_eqToIso _ _ _ p h₁ h he

/-- 同じ単位の端点正規化と後合成は、元の前後合成された単位の値を保持する。 -/
lemma homSpanSectionSourcePrecompIso_postcomp_heq {A E B Y : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) (s : B ⟶ E)
    (hp : IsFullyFaithful p) (hs : s ≫ p = 𝟙 B) (r n : A ⟶ E)
    (hn : n = (r ≫ p) ≫ s) (q : E ⟶ Y) :
    HEq ((homSpanSectionSourcePrecompIso p s hp hs r n hn).postcomp q)
      (((homSpanSectionSourceIso p s hp hs).postcomp q).precomp r) := by
  have he := F2.functorIsoOfEq_heq ((homSpanSectionSourceIso p s hp hs).precomp r)
    ((Category.assoc r p s).symm.trans hn.symm) (Category.comp_id r)
  have hh := F2.functorIso_postcomp_heq_of_heq _ _
    ((Category.assoc r p s).symm.trans hn.symm) (Category.comp_id r) he q
  exact hh.trans (heq_of_eq (F2.functorIso_precomp_postcomp _ r q))

/-- 指定された元の fiber 内比較は、同じ切断の単位の前合成そのもの。 -/
lemma functorIsoOfTrivialKanFibration_eq_sectionUnit {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [TrivialKanFibration p]
    (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) (r n : A ⟶ E)
    (hn : n = (r ≫ p) ≫ s) (h : n ≫ p = r ≫ p) :
    functorIsoOfTrivialKanFibration p n r h =
      homSpanSectionSourcePrecompIso p s (isFullyFaithful_of_trivialKanFibration p)
        hs r n hn := by
  apply (isFullyFaithful_of_trivialKanFibration p).postcomp_functorIso_injective
  rw [functorIsoOfTrivialKanFibration_postcomp,
    homSpanSectionSourcePrecompIso_projection p s _ hs r n hn h]

end SerrePositivity.InfinityCategories
