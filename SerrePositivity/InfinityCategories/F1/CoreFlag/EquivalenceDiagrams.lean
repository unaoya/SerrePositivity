module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.F1.Equivalences.EquivalenceTriangleInitialIso

/-!
概要：全ての辺を可逆に送る図式の全部分圏。
方針：頂点条件で部分圏を作り、指定された始域の収縮から評価の同値を回収する。
規約：図式間の自然変換は全て保持する。core Fun とは異なる転置後の行の模型。
使われ方：Sp-8 の行ごとの定数包含の圏同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
end SerrePositivity.KST.LocalizingInvariants.CoreFlag
namespace SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag
open SerrePositivity.KST.LocalizingInvariants.CoreFlag
open InfinityCategories

/-- 全ての辺を可逆な辺に送る関手という頂点条件。 -/
def IsEquivalenceDiagramVertex (A C : SSet.{u})
    (v : ((ihom A).obj C) _⦋0⦌) : Prop :=
  ∀ e : A _⦋1⦌, IsInvertibleEdge
    (edgeOfSimplex (((functorVertexEquiv A C).symm v).app (Opposite.op ⦋1⦌) e))

/-- 全辺可逆な図式と、それらの間の全ての自然変換。 -/
def equivalenceDiagrams (A C : SSet.{u}) : SSet.{u} :=
  fullSubcomplexOnVertices ((ihom A).obj C) (IsEquivalenceDiagramVertex A C)

/-- 全辺可逆な図式の全関手圏への包含。 -/
def equivalenceDiagramsι (A C : SSet.{u}) : equivalenceDiagrams A C ⟶ (ihom A).obj C :=
  (fullSubcomplexOnVertices _ (IsEquivalenceDiagramVertex A C)).ι

instance equivalenceDiagrams_quasicategory (A C : SSet.{u}) [Quasicategory C] :
    Quasicategory (equivalenceDiagrams A C) := by
  unfold equivalenceDiagrams
  infer_instance

/-- 定値関手は全ての辺を可逆な退化辺に送る。 -/
lemma constant_vertex_mem (A C : SSet.{u}) (c : C _⦋0⦌) :
    IsEquivalenceDiagramVertex A C ((constantFunctorMap A C).app _ c) := by
  rw [constantFunctorMap_vertex]
  change ∀ e : A _⦋1⦌, IsInvertibleEdge
    (edgeOfSimplex (((functorVertexEquiv A C).symm (functorVertexEquiv A C (SSet.const c))).app _ e))
  rw [Equiv.symm_apply_apply]
  intro e
  change IsInvertibleEdge (edgeOfSimplex (PinchedHom.constant c 1))
  exact (isInvertibleEdge_congr (pinchedConstant_one c)).mpr (by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk _)
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance)

/-- 定値図式の包含。 -/
def constant (A C : SSet.{u}) : C ⟶ equivalenceDiagrams A C :=
  fullSubcomplexLift _ (constantFunctorMap A C) (constant_vertex_mem A C)

@[reassoc (attr := simp)]
lemma constant_ι (A C : SSet.{u}) :
    constant A C ≫ equivalenceDiagramsι A C = constantFunctorMap A C :=
  fullSubcomplexLift_ι _ _ _

/-- 指定された始域の頂点で評価する。転置後の行の中でのみ使う。 -/
def evaluation (A C : SSet.{u}) (a : A _⦋0⦌) : equivalenceDiagrams A C ⟶ C :=
  equivalenceDiagramsι A C ≫ evaluateFunctorAt a

@[reassoc (attr := simp)]
lemma constant_evaluation (A C : SSet.{u}) (a : A _⦋0⦌) :
    constant A C ≫ evaluation A C a = 𝟙 C := by
  rw [evaluation, ← Category.assoc, constant_ι]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro c
  change C.map (𝟙 n) c = c
  exact C.map_id_apply n c

/-- 始域の指定された収縮は全辺可逆な図式の上で自然同型を与える。 -/
def evaluation_constant_iso {A C : SSet.{u}} [Quasicategory C]
    (a : A _⦋0⦌) (H : SSet.Homotopy (SSet.const a : A ⟶ A) (𝟙 A)) :
    FunctorIso (evaluation A C a ≫ constant A C) (𝟙 (equivalenceDiagrams A C)) := by
  apply (isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom A).obj C) (IsEquivalenceDiagramVertex A C)).preimageFunctorIso
  have h := functorIsoRestrictedPrecompositionOfHomotopy H (equivalenceDiagramsι A C) (by
    intro v f hf x
    have hv := fullSubcomplexOnVertices_vertex v
    change IsEquivalenceDiagramVertex A C v.val at hv
    change v.val = functorVertex f at hf
    rw [hf] at hv
    have he := hv (simplicialHomotopyVertexEdge H x).edge
    change IsInvertibleEdge (edgeOfSimplex
      (((functorVertexEquiv A C).symm (functorVertexEquiv A C f)).app _ _)) at he
    rw [Equiv.symm_apply_apply] at he
    exact (isInvertibleEdge_congr (e :=
      (simplicialHomotopyVertexEdge H x).toTruncated.map ((truncation 2).map f))
      (f := edgeOfSimplex (f.app _ (simplicialHomotopyVertexEdge H x).edge)) rfl).mpr he)
  change FunctorIso ((evaluation A C a ≫ constant A C) ≫ equivalenceDiagramsι A C)
    (𝟙 (equivalenceDiagrams A C) ≫ equivalenceDiagramsι A C)
  simpa only [Category.assoc, constant_ι, evaluation,
    evaluateFunctorAt_constantFunctorMap, pre_id, NatTrans.id_app,
    Category.comp_id, Category.id_comp] using h

/-- 収縮を持つ始域への定値図式は圏同値。 -/
lemma constant_isQCatEquivalence {A C : SSet.{u}} [Quasicategory C]
    (a : A _⦋0⦌) (H : SSet.Homotopy (SSet.const a : A ⟶ A) (𝟙 A)) :
    IsQCatEquivalence (constant A C) := by
  refine ⟨evaluation A C a, ⟨?_⟩, ⟨evaluation_constant_iso a H⟩⟩
  rw [constant_evaluation]

end SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.IsEquivalenceDiagramVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.IsEquivalenceDiagramVertex := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.IsEquivalenceDiagramVertex

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.constant (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.constant := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.constant

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.constant_evaluation := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.constant_evaluation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.constant_evaluation_assoc := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.constant_evaluation_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.constant_isQCatEquivalence := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.constant_isQCatEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.constant_vertex_mem := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.constant_vertex_mem

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.constant_ι := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.constant_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.constant_ι_assoc := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.constant_ι_assoc

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.equivalenceDiagrams (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.equivalenceDiagrams := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.equivalenceDiagrams

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.equivalenceDiagrams_quasicategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.equivalenceDiagrams_quasicategory := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.equivalenceDiagrams_quasicategory

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.equivalenceDiagramsι (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.equivalenceDiagramsι := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.equivalenceDiagramsι

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.evaluation (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.evaluation := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.evaluation

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.evaluation_constant_iso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.evaluation_constant_iso := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.evaluation_constant_iso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.IsEquivalenceDiagramVertex._proof_1 := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.IsEquivalenceDiagramVertex._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.evaluation.eq_1 := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.evaluation.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.evaluation_constant_iso._proof_1 := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.evaluation_constant_iso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.evaluation_constant_iso._proof_2 := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.evaluation_constant_iso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.evaluation_constant_iso._proof_3 := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.evaluation_constant_iso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.evaluation_constant_iso._proof_4 := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.evaluation_constant_iso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.evaluation_constant_iso._proof_5 := _root_.SerrePositivity.InfinityCategories.F1.CoreFlag.CoreFlag.evaluation_constant_iso._proof_5
