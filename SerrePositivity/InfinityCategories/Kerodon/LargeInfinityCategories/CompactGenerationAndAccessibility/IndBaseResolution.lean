module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.StableInputFunctorLaws
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePullbackPathLifting

/-!
概要：元の accessible な底と Ind 表示の共通自明 Kan 解像を構成する。
方針：元の Ind 表示同値の可逆 path 置換と元の底への厳密な切断を使う。
規約：解像の存在や同値性を主定理への追加入力にしない。
使われ方：Ind 底での入力付き compact 比較同型の元の底への回収。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：元の底と Ind 模型へ向かう共通自明 Kan 解像と元の底の厳密な切断。
方針：実際の可逆 path 置換から得る全射を保持する。
規約：元の底への切断は厳密な射の等式。
使われ方：固定入力と標的を保つ比較同型の反映。 -/
structure IndBaseResolution (μ : Cardinal.{u}) (B : SSet.{u + 1}) where
  generator : SSet.{u}
  generator_quasicategory : Quasicategory generator
  total : SSet.{u + 1}
  total_quasicategory : Quasicategory total
  toModel : total ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ generator
  toBase : total ⟶ B
  model_trivial : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration toModel
  base_trivial : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration toBase
  toResolution : B ⟶ total
  section_property : toResolution ≫ toBase = 𝟙 B

attribute [instance] IndBaseResolution.generator_quasicategory
attribute [instance] IndBaseResolution.total_quasicategory
attribute [instance] IndBaseResolution.model_trivial
attribute [instance] IndBaseResolution.base_trivial

/-- 概要：accessible な元の底には同じ Ind 表示への共通自明 Kan 解像がある。
方針：元の表示同値の path 置換を取り、元の底への自明 Kan 射を切断する。
規約：新しい存在仮定は追加しない。
使われ方：一般 accessible な底での相対交互構成。 -/
lemma nonempty_indBaseResolution_of_isKappaAccessible
    {μ : Cardinal.{u}} {B : SSet.{u + 1}} [Quasicategory B]
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ B) : Nonempty (IndBaseResolution μ B) := by
  obtain ⟨A, hA, ⟨e⟩⟩ := hB.exists_indEquivalence
  have := hA
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection e.hom
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap e.hom
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration r :=
    e.isQCatEquivalence.equivalencePathReplacementMap_trivialKanFibration
  obtain ⟨t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section r
  exact ⟨⟨A, hA, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement e.hom, inferInstance, s, r,
    inferInstance, hr, t, ht⟩⟩

/-- 概要：元の底から Ind 模型への実際の比較射。
方針：元の底の厳密な切断と Ind 模型への射影を合成する。
規約：同じ共通解像を使う。
使われ方：元の入力付き表示を Ind 底へ送る。 -/
def IndBaseResolution.comparison {μ : Cardinal.{u}} {B : SSet.{u + 1}}
    (R : IndBaseResolution μ B) : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ R.generator :=
  R.toResolution ≫ R.toModel

/-- 概要：共通解像から定めた元の底と Ind 模型の比較は全圏の同値。
方針：厳密な切断の合成と二つの自明 Kan 射の同値性を使う。
規約：同値の存在を追加仮定にしない。
使われ方：compact 性と指定 filtered 余極限の輸送。 -/
lemma IndBaseResolution.comparison_isQCatEquivalence
    {μ : Cardinal.{u}} {B : SSet.{u + 1}} [Quasicategory B]
    (R : IndBaseResolution μ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence R.comparison := by
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration R.toBase
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence R.toResolution := by
    apply hr.cancel_right
    rw [R.section_property]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl B).isQCatEquivalence
  exact ht.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration R.toModel)

/-- 概要：Ind 模型には元の底と同じ指定濃度の filtered 余極限が存在する。
方針：構成済みの全比較同値で元の底の余極限を輸送する。
規約：Ind 包含が小さい方の濃度の余極限を保存すると仮定しない。
使われ方：全相対交互図式の元の Ind 圏内での最終余極限。 -/
lemma IndBaseResolution.model_hasSmallKappaFilteredColimits
    {κ μ : Cardinal.{u}} {B : SSet.{u + 1}} [Quasicategory B]
    (R : IndBaseResolution μ B) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ R.generator) :=
  _root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.hasSmallKappaFilteredColimits_of_equivalence R.comparison_isQCatEquivalence.choose hB

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
