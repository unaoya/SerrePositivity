module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.SConstruction.DGOdotMilnorLaxModel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.SourceEquivalencePrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PrecompositionCriterion

/-!
概要：元 Milnor 対角と resolved 商を D2 の実 lax 模型へ二射影比較を保って輸送する。
方針：同じ具体的同値の逆を商の前に合成し、既存の実延長の輸送を適用する。
規約：一般の商・局所化 API は新設せず、元の native 商を終点に保つ。
使われ方：Cat^perf の Tamme 分裂と具体的 Milnor 列の接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonal_isExactFunctor R d
local notation "E" => dgOdotMilnorNativeLaxEquivalence R d

/-- 概要：元の小 Perf 対角を同じ実 lax 模型へ送る包含。
方針：元の native 対角と指定同値を合成する。規約：元の対角作用を保つ。
使われ方：Tamme と Milnor 列の左射。 -/
def dgOdotMilnorLaxInclusion : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonalSource R d)
    (dgOdotMilnorLaxCategory R d) where
  hom := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonal R d).hom ≫ (E).hom
  isExact := by
    letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (E).hom := (dgOdotMilnorNativeLaxComparison R d).isExact
    letI := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonal R d).isExact
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _

/-- 概要：同じ resolved 商へ、実 lax 比較の逆を通って射影する。
方針：native の実商射影を保持する。規約：未分解商へ戻さない。
使われ方：Tamme と Milnor 列の右射。 -/
def dgOdotMilnorLaxProjection : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgOdotMilnorLaxCategory R d)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeResolvedQuotient R d) where
  hom := (E).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).hom
  isExact := by
    letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (E).inv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (E).symm.isQCatEquivalence
    letI := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).isExact
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _

/-- 概要：比較後の射影は同じ元の resolved 射影へ戻る。
方針：指定同値の単位二胞体を後合成する。規約：全関手同型を保持する。
使われ方：元商の二脚・合成三角形の照合。 -/
def dgOdotMilnorLaxProjection_comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((E).hom ≫ (dgOdotMilnorLaxProjection R d).hom)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).hom := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((E).hom ≫ ((E).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).hom)) _
  rw [← Category.assoc]
  simpa only [Category.id_comp] using
    ((E).homInvIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).hom)

/-- 概要：Milnor 条件から同じ lax 包含の充満忠実性。
方針：元対角の証拠と同じ比較同値の充満忠実性を合成する。
規約：個別の充満忠実性を仮定しない。使われ方：列条件の第一欄。 -/
lemma dgOdotMilnorLaxInclusion_fullyFaithful (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (dgOdotMilnorLaxInclusion R d).hom :=
  (dgOdotMilnorNativeSequence R d h).isVerdier.fullyFaithful.comp
    (E).isQCatEquivalence.isFullyFaithful

/-- 概要：lax 射影の零対象核は元対角の同じ輸送像。
方針：native の thick 核を同じ比較の往復二胞体で運ぶ。
規約：対象別の見かけの像だけで核を判定しない。使われ方：列条件の核欄。 -/
lemma dgOdotMilnorLaxKernel (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
    (b : (dgOdotMilnorLaxCategory R d).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((dgOdotMilnorLaxProjection R d).hom.app (Opposite.op ⦋0⦌) b) ↔
      b ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (dgOdotMilnorLaxInclusion R d) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).hom.app (Opposite.op ⦋0⦌)
    ((E).inv.app (Opposite.op ⦋0⦌) b)) ↔ _
  rw [dgOdotMilnorNativeKernel R d h]
  constructor
  · rintro ⟨a, ⟨v⟩⟩
    refine ⟨a, ?_⟩
    change Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((E).hom.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonal R d).hom.app (Opposite.op ⦋0⦌) a)) b)
    exact ⟨(v.map (E).hom).trans ((E).invHomIso.app b)⟩
  · rintro ⟨a, ⟨v⟩⟩
    refine ⟨a, ?_⟩
    exact ⟨((E).homInvIso.app
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonal R d).hom.app (Opposite.op ⦋0⦌) a)).symm.trans
        (v.map (E).inv)⟩

/-- 概要：同じ resolved 射影を持つ具体的 lax 列は実局所化条件を満たす。
方針：native 商の全関手圏の延長を指定同値で戻す既存 API を使う。
規約：任意標的の ∞ 関手圏を保持する。使われ方：Sp の商欄を実証拠で満たす。 -/
lemma dgOdotMilnorLaxLocalization (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (dgOdotMilnorLaxProjection R d).hom
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (dgOdotMilnorLaxInclusion R d))) := by
  letI := (dgOdotMilnorLaxProjection R d).isExact
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (E).hom := (dgOdotMilnorNativeLaxComparison R d).isExact
  have hq := dgOdotMilnorNativeLocalization R d h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization_of_fullyFaithful_extensions
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.inverts_cofiberLocalizingEdges_of_kills _ _
      (fun b hb => (dgOdotMilnorLaxKernel R d h b).2 hb)
  · intro Y hY
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.precomposition_isFullyFaithful_of_sourceEquivalence (E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).hom (hq.precomposition_isFullyFaithful Y)
  · intro Y hY F hF
    have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges ((E).hom ≫ F)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonal R d))) := by
      intro a ha
      obtain ⟨s, z, hz, ⟨v⟩⟩ := ha
      have hm : (E).hom.app (Opposite.op ⦋1⦌) a ∈
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (dgOdotMilnorLaxInclusion R d)) := by
        let t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((E).hom.app (Opposite.op ⦋1⦌) a)) := {
          toZeroTriangle := (s.map (E).hom).toZeroTriangle
          bottom_edge := (s.map (E).hom).bottom_edge
          isPushout := (s.map (E).hom).isPushout }
        refine ⟨t, (E).hom.app (Opposite.op ⦋0⦌) z, ?_, ⟨v.map (E).hom⟩⟩
        obtain ⟨x, ⟨w⟩⟩ := hz
        exact ⟨x, ⟨w.map (E).hom⟩⟩
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
        (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((E).hom.app (Opposite.op ⦋1⦌) a)).map ((truncation 2).map F))
        (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a).map ((truncation 2).map ((E).hom ≫ F))) rfl).mp (hF hm)
    obtain ⟨G, ⟨v⟩⟩ := hq.exists_extension ((E).hom ≫ F) hi
    exact ⟨G, ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.extensionIsoOfSourceEquivalence (E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d).hom F G v⟩⟩

/-- 概要：Milnor 条件だけから同じ lax 包含と resolved 射影の実 Verdier 列。
方針：具体的に輸送した三欄を Sp 正本へ渡す。
規約：追加の核・局所化入力なし。使われ方：Cat^perf の LT 接続。 -/
theorem dgOdotMilnorLax_isVerdier (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence (dgOdotMilnorLaxInclusion R d) (dgOdotMilnorLaxProjection R d) :=
  ⟨dgOdotMilnorLaxInclusion_fullyFaithful R d h,
    dgOdotMilnorLaxKernel R d h, dgOdotMilnorLaxLocalization R d h⟩

end SerrePositivity.KST.SConstruction

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Eq (10)" (partial := component) "仮定：指定された dg Milnor 正方形（Lean が強い）。結論：実 lax gluing と resolved 商の Verdier 列をその冪等完備化まで構成。任意の E₁ 環の主定理の列より狭い（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotMilnorLax_isVerdier
attribute [cite LT "Lemma 1.7" (partial := component) "仮定：指定 dg Milnor 正方形（Lean が強い）。結論：その Perf の対角から native lax への写像の全写像空間での充満忠実性。一般の環スペクトルと RMod は対象外（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotMilnorLaxInclusion_fullyFaithful
