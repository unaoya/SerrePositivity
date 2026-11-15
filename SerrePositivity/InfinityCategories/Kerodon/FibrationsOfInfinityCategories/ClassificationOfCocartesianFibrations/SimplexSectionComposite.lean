module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexSectionBaseChangePasting

/-!
概要：指定全単体底変換の三因子の合成を、同じ端点で比較する。
方針：既存の共同切断合成則に、指定再添字付けと結合括弧の等式だけを適用する。
規約：貼り合わせ比較や底変換同型を選び直さない。
使われ方：Kerodon §5.6（Tag 027M）の分類の指定底変換合成則。
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

/-- 概要：全単体の切断は元の定義域関手の共同切断図式。
方針：元の定義を使う。規約：指定図式を保つ。使われ方：型移送の局所化。 -/
lemma simplexSection_def (T : SSet.{u}) :
    transportSimplexSectionInfinity T = relativeSectionDiagramInfinity
      (transportSimplexDomainFunctor T) := rfl

/-- 概要：標準反復引き戻し比較を元の全単体図式の端点で表示する。
方針：元の図式の定義等式だけで同じ比較を移送する。
規約：比較の実射を変えない。使われ方：指定底変換の三因子の合成。 -/
def simplexSectionCompIso {B D T : SSet.{u}} (k : D ⟶ B) (l : T ⟶ D) :
    FunctorIso
      (transportSimplexSectionInfinity T ≫
        (pre (leftFibrationInfinityBaseChange (l ≫ k))).app SpaceInfinity.{u})
      ((transportSimplexSectionInfinity T ≫
        (pre (leftFibrationInfinityBaseChange l)).app SpaceInfinity.{u}) ≫
        (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}) :=
  diagramIsoCongr
    (congrArg (fun f ↦ f ≫ (pre (leftFibrationInfinityBaseChange (l ≫ k))).app SpaceInfinity.{u})
      (simplexSection_def T).symm)
    (congrArg (fun f ↦ (f ≫ (pre (leftFibrationInfinityBaseChange l)).app SpaceInfinity.{u}) ≫
      (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}) (simplexSection_def T).symm)
    (sectionDiagramBaseChangeCompIso k l (transportSimplexDomainFunctor T))

/-- 概要：第一段の指定底変換を第二段の前合成関手で写し結合括弧を揃える。
方針：後合成した元の同型の終点だけを結合律で移送する。
規約：元の同型を保持する。使われ方：第二段の指定同型との合成。 -/
def simplexSectionFirstIso {B D T : SSet.{u}} (k : D ⟶ B) (l : T ⟶ D) :
    FunctorIso
      ((transportSimplexSectionInfinity T ≫
        (pre (leftFibrationInfinityBaseChange l)).app SpaceInfinity.{u}) ≫
        (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l)) ≫
        (transportSimplexSectionInfinity D ≫
          (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})) :=
  diagramIsoCongr rfl (Category.assoc _ _ _)
    ((transportSimplexSectionInfinity_baseChangeIso l).postcomp
      ((pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}))

/-- 概要：第二段の指定底変換を元の単体圏の制限として表示する。
方針：元の指定同型を前合成する。規約：端点を明示し射を変えない。
使われ方：指定した二段の底変換の合成の最後の因子。 -/
def simplexSectionSecondIso {B D T : SSet.{u}} (k : D ⟶ B) (l : T ⟶ D) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l)) ≫
        (transportSimplexSectionInfinity D ≫
          (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l)) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k)) ≫
          transportSimplexSectionInfinity B)) :=
  (transportSimplexSectionInfinity_baseChangeIso k).precomp
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l)))

/-- 同じ中間端点を持つ二因子の異種等式を合成する証明分割。 -/
private lemma isoTrans_heq {A X : SSet.{u}} {f g h f' g' h' : A ⟶ X}
    (e : FunctorIso f g) (e' : FunctorIso f' g')
    (d : FunctorIso g h) (d' : FunctorIso g' h')
    (hf : f = f') (hg : g = g') (hh : h = h')
    (he : HEq e e') (hd : HEq d d') : HEq (e ≪≫ d) (e' ≪≫ d') := by
  subst f' g' h'
  cases eq_of_heq he
  cases eq_of_heq hd
  rfl

/-- 指定全単体同型は端点移送前の同じ共同切断同型と異種等式で一致する。 -/
private lemma simplexSectionBaseChange_heq {B D : SSet.{u}} (k : D ⟶ B) :
    HEq (transportSimplexSectionInfinity_baseChangeIso k)
      (relativeSectionDiagramInfinityBaseChangeIso k (transportSimplexDomainFunctor D)) :=
  (simplexSectionBaseChange_normalized k).heq.trans
    (diagramIsoCongr_heq rfl (simplexSectionBaseChange_target k)
      (relativeSectionDiagramInfinityBaseChangeIso k (transportSimplexDomainFunctor D)))

/-- 概要：全単体の指定底変換は標準反復引き戻し比較を介して合成を保つ。
方針：共同切断の同じ合成則を、元の単体圏の再添字付けの式で移す。
規約：全図式と同型自身を比較し、頂点ごとの一致には弱めない。
使われ方：Kerodon §5.6（Tag 027M）の指定分類底変換同型の合成則の降下。 -/
lemma transportSimplexSectionInfinity_baseChange_pasting {B D T : SSet.{u}}
    (k : D ⟶ B) (l : T ⟶ D) :
    HEq (simplexSectionCompIso k l ≪≫ simplexSectionFirstIso k l ≪≫
      simplexSectionSecondIso k l)
      (transportSimplexSectionInfinity_baseChangeIso (l ≫ k)) := by
  rw [← Iso.trans_assoc]
  let P := (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}
  let t := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l))
  have hm : t ≫ (transportSimplexSectionInfinity D ≫ P) =
      relativeSectionDiagramInfinity (transportSimplexDomainFunctor T ⋙ Over.map l) ≫ P := by
    rw [← Category.assoc, ← simplexSectionBaseChange_target l]
  have ht : t ≫ ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (transportSimplexFunctor k)) ≫ transportSimplexSectionInfinity B) =
      relativeSectionDiagramInfinity
        ((transportSimplexDomainFunctor T ⋙ Over.map l) ⋙ Over.map k) := by
    rw [← simplexSectionBaseChange_target k, relativeSectionDiagramInfinity_reindex,
      ← Functor.assoc, transportSimplexDomainFunctor_baseChange]
  have hl := Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq
    (relativeSectionDiagramInfinityBaseChangeIso l (transportSimplexDomainFunctor T))
    (transportSimplexSectionInfinity_baseChangeIso l) rfl (simplexSectionBaseChange_target l)
    (simplexSectionBaseChange_heq l) P
  have hfirst : HEq (simplexSectionFirstIso k l)
      ((relativeSectionDiagramInfinityBaseChangeIso l
        (transportSimplexDomainFunctor T)).postcomp P) :=
    (diagramIsoCongr_heq _ _ _).trans hl
  have hk := (simplexSectionBaseChange_reindexed k l).heq.trans
    (diagramIsoCongr_heq _ _ _)
  have h₁ : HEq (simplexSectionCompIso k l ≪≫ simplexSectionFirstIso k l)
      (sectionDiagramBaseChangeCompIso k l (transportSimplexDomainFunctor T) ≪≫
        (relativeSectionDiagramInfinityBaseChangeIso l
          (transportSimplexDomainFunctor T)).postcomp P) := isoTrans_heq
    (simplexSectionCompIso k l)
    (sectionDiagramBaseChangeCompIso k l (transportSimplexDomainFunctor T))
    (simplexSectionFirstIso k l)
    ((relativeSectionDiagramInfinityBaseChangeIso l
      (transportSimplexDomainFunctor T)).postcomp P) rfl rfl hm
    (diagramIsoCongr_heq _ _ _) hfirst
  have h₂ : HEq ((simplexSectionCompIso k l ≪≫ simplexSectionFirstIso k l) ≪≫
        simplexSectionSecondIso k l)
      ((sectionDiagramBaseChangeCompIso k l (transportSimplexDomainFunctor T) ≪≫
        (relativeSectionDiagramInfinityBaseChangeIso l
          (transportSimplexDomainFunctor T)).postcomp P) ≪≫
        relativeSectionDiagramInfinityBaseChangeIso k
          (transportSimplexDomainFunctor T ⋙ Over.map l)) := isoTrans_heq
    (simplexSectionCompIso k l ≪≫ simplexSectionFirstIso k l)
    (sectionDiagramBaseChangeCompIso k l (transportSimplexDomainFunctor T) ≪≫
      (relativeSectionDiagramInfinityBaseChangeIso l (transportSimplexDomainFunctor T)).postcomp P)
    ((transportSimplexSectionInfinity_baseChangeIso k).precomp t)
    (relativeSectionDiagramInfinityBaseChangeIso k
      (transportSimplexDomainFunctor T ⋙ Over.map l)) rfl hm ht h₁ hk.symm
  apply HEq.trans h₂
  apply HEq.trans (Iso.trans_assoc _ _ _).heq
  apply HEq.trans (relativeSectionDiagramInfinityBaseChangeIso_comp k l
    (transportSimplexDomainFunctor T)).heq
  exact (simplexSectionBaseChange_heq (l ≫ k)).symm

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
