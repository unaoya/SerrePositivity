module

public import SerrePositivity.InfinityCategories.Sheaves.DerivedGlobalSections
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpecifiedLimitConeTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.HomotopyBoundaryExtension

/-!
概要：層の元の単位に沿い、頂点を固定して RΓ の全極限錐を元の前層へ戻す。
方針：同じ単位の代表を指定 prism に直し、既存の全錐の輸送を適用する。
  文献対応：HTT 6.2.2.7、Kerodon §7.1（Tag 02H1）の層の大域切断の比較。
規約：独立な頂点の同型を選ばず、指定単位の全時刻の制限を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 同じ層化単位を区間が左側の prism として読む。 -/
def sheafifyUnitPrism (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (F : Presheaf C E) : (Δ[1] : SSet.{u + 1}) ⊗ presheafShape C ⟶ E :=
  (β_ _ _).hom ≫ (sheafifyUnit J hJ F).h

/-- 単位の始点の厳密な制限。 -/
lemma sheafifyUnitPrism_zero (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (F : Presheaf C E) : prismEndpoint 0 _ ≫ sheafifyUnitPrism J hJ F = F := by
  rw [sheafifyUnitPrism, ← Category.assoc, prismEndpoint_zero_braiding]
  exact (sheafifyUnit J hJ F).h₀

/-- 単位の終点の厳密な制限。 -/
lemma sheafifyUnitPrism_one (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (F : Presheaf C E) : prismEndpoint 1 _ ≫ sheafifyUnitPrism J hJ F =
      sheafify J hJ F := by
  rw [sheafifyUnitPrism, ← Category.assoc, prismEndpoint_one_braiding]
  exact (sheafifyUnit J hJ F).h₁

/-- 層では単位の prism は各頂点で可逆。 -/
lemma sheafifyUnitPrism_vertex_isInvertible (J : GrothendieckTopology C)
    (hJ : Sheafification J E) {F : Presheaf C E} (hF : IsSheaf J F)
    (x : (presheafShape C) _⦋0⦌) :
    IsInvertibleEdge (edgeOfSimplex ((sheafifyUnitPrism J hJ F).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})),
        SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) := by
  haveI := sheafifyUnitHom_isIso_of_isSheaf J hJ hF
  have he : IsInvertibleEdge
      (simplicialHomotopyVertexEdge (sheafifyUnit J hJ F) x).toTruncated := by
    change IsIso (Truncated.HomotopyCategory.homMk
      (simplicialHomotopyVertexEdge (functorHomHomotopy (sheafifyUnitHom J hJ F)) x).toTruncated)
    rw [functorHomHomotopy_component]
    infer_instance
  apply (isInvertibleEdge_congr
    (f := (simplicialHomotopyVertexEdge (sheafifyUnit J hJ F) x).toTruncated) ?_).mpr he
  change (sheafifyUnit J hJ F).h.app (Opposite.op ⦋1⦌)
    (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1,
      SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1}))) =
    (sheafifyUnit J hJ F).h.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj (presheafShape C)) x).edge,
        SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})) =
      SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  rw [SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, hi]

/-- 層の指定単位に沿い、頂点と境界の全族を保持して極限錐を戻す。 -/
def sheafUnitLimitConeTransport (J : GrothendieckTopology C) (hJ : Sheafification J E)
    {F : Presheaf C E} (hF : IsSheaf J F)
    (d : JoinCone (sheafify J hJ F)) (hd : IsLimitCone d) :
    SpecifiedLimitConeTransport (p := F) (sheafifyUnitPrism J hJ F) d :=
  specifiedLimitConeTransport _ (sheafifyUnitPrism_zero J hJ F)
    (sheafifyUnitPrism_one J hJ F) (sheafifyUnitPrism_vertex_isInvertible J hJ hF) d hd

/-- RΓ は、層なら元の前層の極限錐の同じ頂点である。 -/
lemma derivedGlobalSections_isLimitVertex_of_isSheaf (J : GrothendieckTopology C)
    (hJ : Sheafification J E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {F : Presheaf C E} (hF : IsSheaf J F) :
    ∃ c : JoinCone F, IsLimitCone c ∧ c.vertex = derivedGlobalSections J hJ hE F := by
  let t := sheafUnitLimitConeTransport J hJ hF (derivedGlobalSectionsCone J hJ hE F)
    (derivedGlobalSectionsCone_isLimit J hJ hE F)
  exact ⟨t.cone, t.isLimit, t.vertex_eq⟩

end SerrePositivity.InfinityCategories.Sheaves
