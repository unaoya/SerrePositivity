module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.StraighteningBaseChangeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TransposeFunctorIsoRestriction

/-!
概要：指定した分類底変換同型の初頂点制限を、同じ共同切断比較の転置として読む。
方針：転置の二つの端点移送を消去し、指定充満忠実逆像の制限則を使う。
規約：別の比較同型の存在には置き換えない。
使われ方：Kerodon §5.6（Tag 027M）の分類底変換の貼り合わせ法則の降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

private lemma two_mp_heq {α β γ : Sort v} (h₁ : α = β) (h₂ : β = γ) (x : α) :
    HEq (Eq.mp h₂ (Eq.mp h₁ x)) x := by
  cases h₁
  cases h₂
  rfl

/-- 概要：指定分類底変換は同じ共同図式の底変換を転置したものと端点移送だけ異なる。
方針：元の定義の二回の型移送を消去する。
規約：指定同型自身の異種等式。使われ方：初頂点制限での同じ比較の計算。 -/
lemma leftStraighteningInfinityMap_baseChangeIso_heq_transpose {B D : SSet.{u}} (k : D ⟶ B) :
    HEq (leftStraighteningInfinityMap_baseChangeIso k)
      (leftStraighteningSectionJointDiagram_baseChangeIso k).transpose := by
  unfold leftStraighteningInfinityMap_baseChangeIso
  exact two_mp_heq _ _ _

/-- 概要：指定分類底変換の初頂点制限は、同じ切断制限同型の転置。
方針：前合成と転置の合成則に、指定降下同型の厳密な制限則を適用する。
規約：同じ関手同型全体を比較する。使われ方：指定分類底変換の合成則を切断図式へ戻す。 -/
lemma leftStraighteningInfinityMap_baseChangeIso_firstVertex_heq {B D : SSet.{u}}
    (k : D ⟶ B) :
    HEq ((leftStraighteningInfinityMap_baseChangeIso k).postcomp
      ((pre ((SSet.uliftFunctor.{u + 1, u}).map
        (transportSimplexFirstVertexMap D))).app SpaceInfinity.{u}))
      (straighteningBaseChangeRestrictionIso k).transpose := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let q := U.map (transportSimplexFirstVertexMap D)
  let e := leftStraighteningSectionJointDiagram_baseChangeIso k
  have hf : leftStraighteningInfinityMap B ≫ (pre (U.map k)).app SpaceInfinity.{u} =
      transposeFunctorFamily (U.map k ≫ leftStraighteningSectionJointDiagram B) :=
    (transposeFunctorFamily_comp (U.map k) (leftStraighteningSectionJointDiagram B)).symm
  have hg : leftFibrationInfinityBaseChange k ≫ leftStraighteningInfinityMap D =
      transposeFunctorFamily (leftStraighteningSectionJointDiagram D ≫
        (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}) :=
    (transposeFunctorFamily_pre (leftStraighteningSectionJointDiagram D)
      (leftFibrationInfinityBaseChange k)).symm
  have hp := Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq
    (leftStraighteningInfinityMap_baseChangeIso k) e.transpose hf hg
    (leftStraighteningInfinityMap_baseChangeIso_heq_transpose k) ((pre q).app SpaceInfinity.{u})
  have ht := functorIsoTranspose_precomp q e
  have h : HEq ((leftStraighteningInfinityMap_baseChangeIso k).postcomp
        ((pre q).app SpaceInfinity.{u})) (e.precomp q).transpose :=
    hp.trans (ht.symm.heq.trans (diagramIsoCongr_heq _ _ _))
  simpa only [e, q, U, straighteningBaseChangeIso_firstVertex] using h

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
