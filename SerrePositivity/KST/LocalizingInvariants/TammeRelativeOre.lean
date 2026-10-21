module

public import SerrePositivity.KST.LocalizingInvariants.PullbackDiagramFamilies
public import SerrePositivity.KST.LocalizingInvariants.TammeUniversalOre
public import SerrePositivity.InfinityCategories.Core.EquivalencePathReplacement

/-!
概要：Tamme 分母を片脚に持つ cospan の普遍 Ore 補完は、相対高次族として構成できる。
方針：指定分母の cospan の全部分複体へ普遍 pullback 射影を基底変更する。
規約：元の cospan と既存の部分族を厳密に保持し、各四角形の下辺も元の分母となる。
使われ方：局所化後の写像空間の全境界に対する coherent な分母の細分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

def IsTammeDenominatorCospan
    (v : ((ihom (horn 2 2 : SSet.{u})).obj (laxCategory p q).obj) _⦋0⦌) : Prop :=
  SSet.yonedaEquiv (horn₂₂.ι₁₂ ≫
    (functorVertexEquiv (horn 2 2 : SSet.{u}) (laxCategory p q).obj).symm v) ∈
      tammeLocalizingEdges p q

def tammeDenominatorCospans : SSet.{u} :=
  (fullSubcomplexOnVertices _ (IsTammeDenominatorCospan p q) : SSet.{u})

instance tammeDenominatorCospans_quasicategory : Quasicategory (tammeDenominatorCospans p q) :=
  fullSubcomplexOnVertices_quasicategory _ _

def tammeDenominatorCospanInclusion : tammeDenominatorCospans p q ⟶
    (ihom (horn 2 2 : SSet.{u})).obj (laxCategory p q).obj :=
  (fullSubcomplexOnVertices _ (IsTammeDenominatorCospan p q)).ι

def tammeOreDiagrams : SSet.{u} :=
  pullback (pullbackProjection (laxCategory p q).obj) (tammeDenominatorCospanInclusion p q)

def tammeOreProjection : tammeOreDiagrams p q ⟶ tammeDenominatorCospans p q :=
  pullback.snd _ _

instance tammeOreProjection_trivialKanFibration : TrivialKanFibration (tammeOreProjection p q) :=
  trivialKanFibration_pullback_snd _ _

instance tammeOreDiagrams_quasicategory : Quasicategory (tammeOreDiagrams p q) :=
  quasicategory_of_innerFibration (tammeOreProjection p q)

def tammeOreSquare (v : (tammeOreDiagrams p q) _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (laxCategory p q).obj :=
  (functorVertexEquiv _ _).symm
    ((pullback.fst (pullbackProjection (laxCategory p q).obj)
      (tammeDenominatorCospanInclusion p q)).app (Opposite.op ⦋0⦌) v).val

lemma tammeOreSquare_isPullback (v : (tammeOreDiagrams p q) _⦋0⦌) :
    IsPullbackSquare (tammeOreSquare p q v) :=
  fullSubcomplexOnVertices_vertex ((pullback.fst (pullbackProjection (laxCategory p q).obj)
    (tammeDenominatorCospanInclusion p q)).app (Opposite.op ⦋0⦌) v)

lemma tammeOreSquare_cospan (v : (tammeOreDiagrams p q) _⦋0⦌) :
    pullbackCospan (tammeOreSquare p q v) =
      (functorVertexEquiv (horn 2 2 : SSet.{u}) (laxCategory p q).obj).symm
        (((tammeOreProjection p q).app (Opposite.op ⦋0⦌) v).val) := by
  apply (functorVertexEquiv (horn 2 2 : SSet.{u}) (laxCategory p q).obj).injective
  rw [(functorVertexEquiv _ _).apply_symm_apply]
  have hr : functorVertex (tammeOreSquare p q v) =
      ((pullback.fst (pullbackProjection (laxCategory p q).obj)
        (tammeDenominatorCospanInclusion p q)).app (Opposite.op ⦋0⦌) v).val :=
    (functorVertexEquiv _ _).apply_symm_apply _
  change ((pre cospanSquareBoundary).app (laxCategory p q).obj).app (Opposite.op ⦋0⦌)
    (functorVertex (tammeOreSquare p q v)) = _
  rw [hr]
  have hc :
      pullback.fst (pullbackProjection (laxCategory p q).obj)
          (tammeDenominatorCospanInclusion p q) ≫ pullbackProjection (laxCategory p q).obj =
        tammeOreProjection p q ≫ tammeDenominatorCospanInclusion p q := pullback.condition
  exact congrArg (fun k : tammeOreDiagrams p q ⟶
      (ihom (horn 2 2 : SSet.{u})).obj (laxCategory p q).obj =>
    k.app (Opposite.op ⦋0⦌) v) hc

lemma tammeOreSquare_top_mem (v : (tammeOreDiagrams p q) _⦋0⦌) :
    (squareTopArrow (tammeOreSquare p q v)).edge ∈ tammeLocalizingEdges p q := by
  have hv := fullSubcomplexOnVertices_vertex ((tammeOreProjection p q).app (Opposite.op ⦋0⦌) v)
  change SSet.yonedaEquiv (horn₂₂.ι₁₂ ≫ _) ∈ tammeLocalizingEdges p q at hv
  rw [← tammeOreSquare_cospan, pullbackCospan, ← Category.assoc,
    cospanSquareBoundary_topEdge] at hv
  exact (squareTopArrow_edge (tammeOreSquare p q v)).symm ▸ hv

lemma tammeOreSquare_bottom_mem (v : (tammeOreDiagrams p q) _⦋0⦌) :
    (squareBottomArrow (tammeOreSquare p q v)).edge ∈ tammeLocalizingEdges p q :=
  (tammeLocalizingEdges_pullback_bottom_top p q _ (tammeOreSquare_isPullback p q v)).mpr
    (tammeOreSquare_top_mem p q v)

lemma exists_relative_tammeOreFamily {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (d : B ⟶ tammeDenominatorCospans p q) (a : A ⟶ tammeOreDiagrams p q)
    (ha : a ≫ tammeOreProjection p q = i ≫ d) :
    ∃ F : B ⟶ tammeOreDiagrams p q, i ≫ F = a ∧ F ≫ tammeOreProjection p q = d := by
  have := TrivialKanFibration.mem (p := tammeOreProjection p q) i inferInstance
  have sq : CommSq a i (tammeOreProjection p q) d := ⟨ha⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

def tammeOreFamilySpace {B : SSet.{u}} (d : B ⟶ tammeDenominatorCospans p q) : SSet.{u} :=
  vertexFiber ((ihom B).map (tammeOreProjection p q)) (functorVertex d)

lemma tammeOreFamilySpace_isContractibleKan {B : SSet.{u}}
    (d : B ⟶ tammeDenominatorCospans p q) : IsContractibleKan (tammeOreFamilySpace p q d) :=
  vertexFiber_isContractibleKan ((ihom B).map (tammeOreProjection p q)) (functorVertex d)

def tammeOreFamiliesIso {B : SSet.{u}} (d : B ⟶ tammeDenominatorCospans p q)
    (F G : B ⟶ tammeOreDiagrams p q)
    (hF : F ≫ tammeOreProjection p q = d) (hG : G ≫ tammeOreProjection p q = d) :
    FunctorIso F G :=
  functorIsoOfTrivialKanFibration (tammeOreProjection p q) F G (hF.trans hG.symm)

end SerrePositivity.KST.LocalizingInvariants
