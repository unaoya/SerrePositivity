module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus
public import SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion.RetractClosure
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityFullyFaithful
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping

/-!
概要：元の前層 ∞ 圏内で Yoneda 像の retract 閉包を構成する。
方針：元の Yoneda 像の頂点を指定し、その retract を全部分複体に取る。
規約：冪等完備性と普遍性は後続の定理で証明する。定義の入力に仮定しない。
使われ方：HTT 5.1.4.2 の Idem(C) の具体的な対象と包含。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の Yoneda の像に属する前層の頂点。 -/
def IsYonedaVertex {C : SSet.{u}} [Quasicategory C]
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌) : Prop :=
  ∃ x : C _⦋0⦌, F = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up x)

/-- 元の前層圏内の、元の Yoneda 像の retract である頂点。 -/
def IsRetractPresheaf {C : SSet.{u}} [Quasicategory C]
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌) : Prop := _root_.SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion.retractClosure IsYonedaVertex F

/-- 元の Yoneda 像の retract は、さらに retract を取っても同じ条件を満たす。 -/
lemma isRetractPresheaf_of_retract {C : SSet.{u}} [Quasicategory C]
    {F G : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf F G)
    (hG : IsRetractPresheaf G) : IsRetractPresheaf F := _root_.SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion.retractClosure_of_retract h hG

/-- 元の Yoneda 像の retract の条件は、元の前層の頂点同型で不変。 -/
lemma isRetractPresheaf_iff_of_iso {C : SSet.{u}} [Quasicategory C]
    {F G : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso F G) :
    IsRetractPresheaf F ↔ IsRetractPresheaf G := _root_.SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion.retractClosure_iff_of_iso IsYonedaVertex e

/-- 元の前層圏内の Yoneda 像の retract 閉包としての Idem(C)。 -/
def Idem (C : SSet.{u}) [Quasicategory C] : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) IsRetractPresheaf

/-- 元の retract 閉包は全部分 quasicategory。 -/
instance idem_quasicategory (C : SSet.{u}) [Quasicategory C] : Quasicategory (Idem C) :=
  inferInstanceAs (Quasicategory
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) IsRetractPresheaf : SSet.{u + 1}))

/-- 元の前層圏への包含。 -/
def idemInclusionPresheaf (C : SSet.{u}) [Quasicategory C] : Idem C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) IsRetractPresheaf).ι

/-- 元の包含は元の写像空間で充満忠実。 -/
lemma idemInclusionPresheaf_isFullyFaithful (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (idemInclusionPresheaf C) := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _

/-- 元の全 Yoneda 関手を、元の retract 閉包へ全単体ごと因子化する。 -/
def idemYoneda (C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ Idem C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsRetractPresheaf (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) (fun a ↦ by
    obtain ⟨x⟩ := a
    exact _root_.SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion.mem_retractClosure ⟨x, rfl⟩)

/-- 元の包含後に、元の全 Yoneda 関手そのものを回収する。 -/
lemma idemYoneda_inclusion (C : SSet.{u}) [Quasicategory C] :
    idemYoneda C ≫ idemInclusionPresheaf C = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 元の retract 閉包への同じ Yoneda は充満忠実。 -/
lemma idemYoneda_isFullyFaithful (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (idemYoneda C) := by
  apply (idemInclusionPresheaf_isFullyFaithful C).cancel_right
  rw [idemYoneda_inclusion]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_isFullyFaithful C

/-- 元の閉包の各対象は、元の前層圏内で指定された元の Yoneda 対象の retract。 -/
lemma idemVertex_retract_yoneda {C : SSet.{u}} [Quasicategory C] (F : (Idem C) _⦋0⦌) :
    ∃ x : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf
      ((idemInclusionPresheaf C).app (Opposite.op ⦋0⦌) F)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up x)) := by
  obtain ⟨G, ⟨x, rfl⟩, h⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex F
  exact ⟨x, h⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
