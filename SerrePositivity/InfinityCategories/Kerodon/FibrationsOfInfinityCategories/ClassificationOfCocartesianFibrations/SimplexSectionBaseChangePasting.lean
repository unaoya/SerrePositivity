module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionDiagramBaseChangePasting
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.StraighteningBaseChangeRestriction
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransportAlgebra

/-!
概要：指定した全単体の切断底変換同型の反復合成。
方針：共同切断の合成則を単体圏へ特殊化し、指定の再添字付けを保持する。
規約：元の標準引き戻し比較を変えない。
使われ方：Kerodon §5.6（Tag 027M）の分類における指定底変換合成則の降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

/-- 概要：共同切断底変換の終点は、元の単体圏の再添字付けと同じ図式。
方針：元の定義域関手の底変換と切断の再添字付けを使う。
規約：任意の底写像を許す。使われ方：指定した全単体同型の端点の正規化。 -/
lemma simplexSectionBaseChange_target {B D : SSet.{u}} (k : D ⟶ B) :
    relativeSectionDiagramInfinity (transportSimplexDomainFunctor D ⋙ Over.map k) =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k)) ≫
        transportSimplexSectionInfinity B := by
  rw [← transportSimplexDomainFunctor_baseChange]
  exact (transportSimplexSectionInfinity_reindex (transportSimplexFunctor k)).symm

/-- 二重の型移送を一段ずつ除く。同じ指定値の簡約を局所化する証明分割。 -/
private lemma two_mpr_heq {α β γ : Sort (u + 2)}
    (h₁ : α = β) (h₂ : β = γ) (x : γ) :
    HEq (Eq.mpr h₁ (Eq.mpr h₂ x)) x := by
  cases h₁
  cases h₂
  rfl

/-- 概要：指定した全単体底変換同型は、元の共同切断比較の同じ端点移送。
方針：既存定義の書き換えによる移送を異種等式で除去する。
規約：同型を選び直さない。使われ方：指定同型の合成則を共同切断から回収する。 -/
lemma simplexSectionBaseChange_normalized {B D : SSet.{u}} (k : D ⟶ B) :
    transportSimplexSectionInfinity_baseChangeIso k =
      diagramIsoCongr rfl (simplexSectionBaseChange_target k)
        (relativeSectionDiagramInfinityBaseChangeIso k (transportSimplexDomainFunctor D)) := by
  have he : HEq (transportSimplexSectionInfinity_baseChangeIso k)
      (relativeSectionDiagramInfinityBaseChangeIso k (transportSimplexDomainFunctor D)) := by
    unfold transportSimplexSectionInfinity_baseChangeIso
    exact two_mpr_heq _ _ _
  exact eq_of_heq (he.trans (diagramIsoCongr_heq rfl (simplexSectionBaseChange_target k)
    (relativeSectionDiagramInfinityBaseChangeIso k (transportSimplexDomainFunctor D))).symm)

/-- 係数関手の等式は同じ指定同型の異種等式を与える。再添字付けの証明分割。 -/
private lemma sectionBaseChangeIso_coeff_heq {B D : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) {A A' : Jᵒᵖ ⥤ Over D}
    (h : A = A') : HEq (relativeSectionDiagramInfinityBaseChangeIso k A)
      (relativeSectionDiagramInfinityBaseChangeIso k A') := by
  subst A'
  rfl

/-- 両端点を保った同型の異種等式は、同じ前合成で保たれる。 -/
private lemma isoPrecomp_heq {W X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : FunctorIso f g) (e' : FunctorIso f' g') (hf : f = f') (hg : g = g')
    (he : HEq e e') (q : W ⟶ X) : HEq (e.precomp q) (e'.precomp q) := by
  subst f' g'
  cases eq_of_heq he
  rfl

/-- 概要：単体圏へ制限した第二段の元の共同底変換同型を同じ指定同型で回収する。
方針：指定共同比較の添字制限則と元の定義域関手の底変換を使う。
規約：全単体上の同じ自然変換を比較する。使われ方：反復底変換の中間因子。 -/
lemma simplexSectionBaseChange_reindexed {B D T : SSet.{u}}
    (k : D ⟶ B) (l : T ⟶ D) :
    relativeSectionDiagramInfinityBaseChangeIso k
        (transportSimplexDomainFunctor T ⋙ Over.map l) =
      diagramIsoCongr
        (by rw [← Category.assoc, ← simplexSectionBaseChange_target l])
        (by rw [← simplexSectionBaseChange_target k, relativeSectionDiagramInfinity_reindex,
          ← Functor.assoc, transportSimplexDomainFunctor_baseChange])
        ((transportSimplexSectionInfinity_baseChangeIso k).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l)))) := by
  have h₁ := sectionBaseChangeIso_coeff_heq k
    (transportSimplexDomainFunctor_baseChange l).symm
  have h₂ := relativeSectionDiagramInfinityBaseChangeIso_reindex k
    (transportSimplexDomainFunctor D) (transportSimplexFunctor l)
  have h₃ : HEq (relativeSectionDiagramInfinityBaseChangeIso k
        (transportSimplexDomainFunctor D))
      (transportSimplexSectionInfinity_baseChangeIso k) :=
    ((simplexSectionBaseChange_normalized k).heq.trans
      (diagramIsoCongr_heq rfl (simplexSectionBaseChange_target k)
        (relativeSectionDiagramInfinityBaseChangeIso k (transportSimplexDomainFunctor D)))).symm
  have h₄ := isoPrecomp_heq _ _ rfl (simplexSectionBaseChange_target k) h₃
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l)))
  apply eq_of_heq
  exact h₁.trans (h₂.heq.trans ((diagramIsoCongr_heq _ _ _).trans
    (h₄.trans (diagramIsoCongr_heq _ _ _).symm)))


end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
