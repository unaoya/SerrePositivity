module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PartialColimitEndInitiality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PartialColimitSpanHomEnd

/-!
概要：既知の普遍 span の全 Hom の族を共通 path end へ移し、元の余錐との比較の正確な標的にする。
方針：native な span の余極限性を strict 表示へ移し、既存の二つの end 比較の同値を合成する。
規約：元の余錐の族とのホモトピーは未証明の入力として明示。使われ方：残る経路の整合性の検証箇所。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)

/-- 既知の普遍 span の全 Hom の族から、元の図式側と同じ共通 path end への実際の射。 -/
def nativeSpanUniversalFamilyToPathEnd :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
        g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC).vertex y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomPathEnd hp p y c hc dB dC :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
      g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC) y ≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanCoconeToHomEnd hp p c hc dB dC y ≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomEndToPathEnd hp p y c hc dB dC

/-- 普遍 span 側の全 Hom の族の共通 path end への比較は、無条件にホモトピー同値。 -/
lemma nativeSpanUniversalFamilyToPathEnd_homotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (nativeSpanUniversalFamilyToPathEnd hp p c hc dB dC y) := by
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
      g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC) :=
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram _).symm _).mp
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitPushoutCocone_isColimit c hc f (i ≫ p) rfl dB
        g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u + 1} WalkingCospan))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomCospan hp p y c hc dB dC)) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedSections_kanComplex _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily_homotopyEquivalence _ ht y).comp
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanCoconeToHomEnd_homotopyEquivalence hp p c hc dB dC y).comp
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomEndToPathEnd_homotopyEquivalence hp p y c hc dB dC))

variable [Mono g]

/-- 指定経路で構成した余錐の頂点は、同じ strict な普遍 span の頂点そのもの。 -/
lemma specifiedPathCocone_vertex_eq_strictSpan :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
        g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC).vertex :=
  (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedBoundaryFamily hp p c hc dB dC)).property.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _)

/-- 同じ実際の頂点の左 Hom で表示した、比較先の普遍 span の共通 path end への族。 -/
def specifiedCoconeNativeFamilyToPathEnd :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomPathEnd hp p y c hc dB dC :=
  eqToHom (congrArg (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft v y)
      (specifiedPathCocone_vertex_eq_strictSpan hp p c hc dB dC)) ≫
    nativeSpanUniversalFamilyToPathEnd hp p c hc dB dC y

/-- 頂点の表示を揃えた比較先も、共通 path end への実際のホモトピー同値。 -/
lemma specifiedCoconeNativeFamilyToPathEnd_homotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (specifiedCoconeNativeFamilyToPathEnd hp p c hc dB dC y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso _).comp
    (nativeSpanUniversalFamilyToPathEnd_homotopyEquivalence hp p c hc dB dC y)

/-- 残る全パラメータの族のホモトピーが得られれば、構成した元の余錐の余極限性を結論できる。 -/
lemma specifiedPathCocone_isColimit_of_pathFamily_homotopy
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dB) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dC)
    (h : ∀ y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌, Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomFamilyToPathEnd hp p c hc dB hB dC hC
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC) y)
      (specifiedCoconeNativeFamilyToPathEnd hp p c hc dB dC y))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.isColimitCone_iff_partialColimitHomFamilyToPathEnd hp p c hc dB hB dC hC _).mpr
  intro z
  obtain ⟨H⟩ := h z
  have hh := specifiedCoconeNativeFamilyToPathEnd_homotopyEquivalence hp p c hc dB dC z
  have he := hh.isQCatEquivalence
  exact (he.ofFunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H).symm).isSimplicialHomotopyEquivalence

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
