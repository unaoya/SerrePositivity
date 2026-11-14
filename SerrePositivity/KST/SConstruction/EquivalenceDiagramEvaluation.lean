module
public import SerrePositivity.KST.SConstruction.RestrictedPrecompositionIso
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.SimplexInitialContraction
public import SerrePositivity.KST.SConstruction.FunctorVertexEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexFunctorFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence

/-! # D(m,w) の零頂点での評価の自明ファイブレーション
概要：全同値な標準単体の図式の零頂点での評価は trivial Kan fibration。
方針：零頂点からの収縮を自然同値へ移し、inner fibration・充満忠実性・頂点の全射性を合わせる。
規約：object/core 比較を仮定しない。使われ方：Fiore–Pieper Proposition 4.27 の行の弱同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：定値自己射による前合成は指定頂点での評価と定数図式の合成。
方針：定値射を一点経由で分解し、一点からの内部 Hom の同型を使う。
規約：添字と標的は任意。使われ方：収縮の始点と評価の合成の照合。 -/
lemma pre_constant_evaluation {K C : SSet.{u}} (k : K _⦋0⦌) :
    (pre (SSet.const k : K ⟶ K)).app C = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k ≫ curry (snd K C) := by
  let t := stdSimplex.isTerminalObj₀.from K
  have ht : (pointFunctorEvaluationIso C).inv ≫ (pre t).app C = curry (snd K C) := by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry]
    change t ▷ C ≫ uncurry (curry (snd (Δ[0] : SSet.{u}) C)) = _
    rw [uncurry_curry]
    rfl
  have ht' : (pre t).app C = (pointFunctorEvaluationIso C).hom ≫ curry (snd K C) := by
    apply (cancel_epi (pointFunctorEvaluationIso C).inv).1
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact ht
  have hk : t ≫ SSet.yonedaEquiv.symm k = SSet.const k := by
    rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const]
  rw [← hk, pre_map, NatTrans.comp_app, ht', ← Category.assoc, evaluateFunctorAt_factor]

/-- 概要：標準単体の零頂点から恒等射への実際のホモトピー。
方針：第一因子に時刻を置いた収縮を交換する。
規約：ホモトピーの時刻は第二因子。使われ方：全同値図式の自然同値。 -/
def simplexInitialHomotopy (n : ℕ) :
    SSet.Homotopy (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))
      (𝟙 (Δ[n] : SSet.{u})) where
  h := (β_ (Δ[n] : SSet.{u}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplexInitialContraction n
  h₀ := by
    rw [← Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[n] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplexInitialContraction n = _
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplexInitialContraction_zero n
  h₁ := by
    rw [← Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[n] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplexInitialContraction n = _
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplexInitialContraction_one n
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：全同値図式を評価して定数図式に戻す合成は恒等関手と自然同値。
方針：添字の収縮の各成分は全同値図式の下で可逆となり、充満包含で同型を持ち上げる。
規約：元の全同値図式の圏における関手同型。使われ方：評価の同値と充満忠実性。 -/
def equivalenceDiagramEvaluation_comparison (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (equivalenceDiagramEvaluation (Δ[n] : SSet.{u}) C (stdSimplex.obj₀Equiv.symm 0) ≫
        equivalenceDiagramConstant Δ[n] C) (𝟙 (equivalenceDiagrams Δ[n] C)) := by
  let E := equivalenceDiagrams (Δ[n] : SSet.{u}) C
  let ι := equivalenceDiagramι (Δ[n] : SSet.{u}) C
  let p := equivalenceDiagramEvaluation (Δ[n] : SSet.{u}) C (stdSimplex.obj₀Equiv.symm 0)
  let s := equivalenceDiagramConstant (Δ[n] : SSet.{u}) C
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (ι ≫ (pre (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) :
        (Δ[n] : SSet.{u}) ⟶ Δ[n])).app C)
      (ι ≫ (pre (𝟙 (Δ[n] : SSet.{u}))).app C) := by
    exact restrictedPrecompositionIso (simplexInitialHomotopy n) ι (fun v a =>
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (simplexInitialHomotopy n) a).edge)
  have hs : (p ≫ s) ≫ ι = ι ≫ (pre (SSet.const (stdSimplex.obj₀Equiv.symm
      (0 : Fin (n + 1))))).app C := by
    rw [pre_constant_evaluation, ← Category.assoc]
    change (p ≫ s) ≫ ι = p ≫ curry (snd (Δ[n] : SSet.{u}) C)
    rw [Category.assoc, equivalenceDiagramConstant_ι]
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((p ≫ s) ≫ ι) ((𝟙 E) ≫ ι) := by
    rw [Category.id_comp, hs]
    simpa only [pre_id, NatTrans.id_app, Category.comp_id] using e
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexFunctorInclusion E ((ihom (Δ[n] : SSet.{u})).obj C)
    IsEquivalenceDiagramVertex).preimageVertexIso
  exact he

/-- 概要：全同値図式の零頂点での評価は quasicategory の同値。
方針：定数図式を逆、収縮による関手同型と厳密な切断を比較に使う。
規約：標的の quasicategory 性のみ。使われ方：評価の充満忠実性。 -/
def equivalenceDiagramEvaluationEquivalence (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (equivalenceDiagrams (Δ[n] : SSet.{u}) C) C where
  hom := equivalenceDiagramEvaluation Δ[n] C (stdSimplex.obj₀Equiv.symm 0)
  inv := equivalenceDiagramConstant Δ[n] C
  homInvIso := equivalenceDiagramEvaluation_comparison n C
  invHomIso := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration (𝟙 C) _ _ (by
    rw [Category.comp_id, Category.id_comp, equivalenceDiagramConstant_evaluation])

/-- 概要：D(m,w) の零頂点での評価は trivial Kan fibration。
方針：inner fibration 性、自然同値からの充満忠実性、定数図式による頂点の全射性を合わせる。
規約：零次数を含む全ての m。使われ方：object S による行の弱同値の比較。 -/
instance equivalenceDiagramEvaluation_trivialKanFibration (n : ℕ) (C : SSet.{u})
    [Quasicategory C] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration
      (equivalenceDiagramEvaluation (Δ[n] : SSet.{u}) C (stdSimplex.obj₀Equiv.symm 0)) := by
  let e := equivalenceDiagramEvaluationEquivalence n C
  have : InnerFibration e.hom := equivalenceDiagramEvaluation_innerFibration _ _ _
  apply e.isFullyFaithful.trivialKanFibration_of_surjective
  intro c
  refine ⟨(equivalenceDiagramConstant (Δ[n] : SSet.{u}) C).app (Opposite.op ⦋0⦌) c, ?_⟩
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (equivalenceDiagramConstant_evaluation (Δ[n] : SSet.{u}) C
      (stdSimplex.obj₀Equiv.symm 0)) (Opposite.op ⦋0⦌)) c

end SerrePositivity.KST.SConstruction
