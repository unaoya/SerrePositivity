module


public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSections
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.QCatEquivalence
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.UniverseConeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PointConeLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PointJoinNerveExt
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SimplexConeRestriction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableSmallLimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.EquivalentConeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeNaturality
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Sites.Sieves.Presheaf
public import SerrePositivity.InfinityCategories.Sheaves.GlobalSections
public import SerrePositivity.InfinityCategories.Sheaves.SieveSectionsDiagram

/-!
概要：集合重みの指定切断錐を、元の篩の制限錐へ接続する。
方針：既存のG8の射と錐の普遍性を使い、全錐の再添字を照合する。
  文献対応：HTT 6.2.2.6、Kerodon §7.1（Tag 02H1）の層条件の切断表示。
規約：元の指定錐・比較辺を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Sheaves
variable {𝒞 : Type u} [SmallCategory 𝒞] {E : SSet.{u+1}} [Quasicategory E]

/-- 概要：E が表示可能なら上の図式は極限をもつ（添字は小さい）。 -/
theorem sectionsOfDiagram_hasLimit (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (sectionsOfDiagram F O) := hE.hasLimit _

/-- 概要：S8-4：切断 Γ(F, O) := lim_{el(F)} O（重み付き極限）。選んだ極限錐の頂点。
方針：S2 の `globalSections` と同じ選び方。
規約：E 表示可能（`HasLimit` を引数で受ける）。
使われ方：Cor 8.12 の引き戻し。 -/
def sectionsOfCone (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (sectionsOfDiagram F O)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (sectionsOfDiagram F O) :=
  h.choose
def sectionsOf (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (sectionsOfDiagram F O)) : E _⦋0⦌ :=
  (sectionsOfCone F O h).vertex
theorem sectionsOfCone_isLimit (F : 𝒞ᵒᵖ ⥤ Type u) (O : Presheaf 𝒞 E) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (sectionsOfDiagram F O)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (sectionsOfCone F O h) := h.choose_spec

/-- 概要：Γ(−, O) の関手性：φ : P ⟶ Q に対し Γ(Q, O) → Γ(P, O)（元の圏の関手 P.Elements ⥤ Q.Elements に沿う制限と極限の普遍性）。
方針：錐の制限。
規約：E の辺。本体は IF-G2 の `SetWeight.sectionsMap φ O (sectionsOfCone P O hP) (sectionsOfCone_isLimit …)
  (sectionsOfCone Q O hQ) (sectionsOfCone_isLimit …)`（Γ(Q) → Γ(P)、G2 停止点 1 で承認）
をそのまま使う。図式 `sectionsOfDiagram` は ∞ 側の `SetWeight.diagram` と同じ式（`Functor.Elements.π` の nerve を前合成）。
縦の比較は `SetWeight.tensorSpaceFunctor_setWeightHomNatural`。S4 は篩包含の場合の自然性だけを使い、
一般の φ の自然性は S8-5 用に待つ（IF-G2）。
使われ方：`sections_localEquiv_iso`、押し出しの比較。 -/
def sectionsOf_map {P Q : 𝒞ᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (O : Presheaf 𝒞 E)
    (hP : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (sectionsOfDiagram P O)) (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (sectionsOfDiagram Q O)) :
    SSet.Edge (sectionsOf Q O hQ) (sectionsOf P O hP) :=
  _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.sectionsMap φ O (sectionsOfCone P O hP) (sectionsOfCone_isLimit P O hP)
    (sectionsOfCone Q O hQ) (sectionsOfCone_isLimit Q O hQ)


end SerrePositivity.InfinityCategories.Sheaves
