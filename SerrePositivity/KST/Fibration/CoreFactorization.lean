module
public import SerrePositivity.KST.Fibration.WeakStringsStability
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.InnerAnodyneEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreKan
public import Mathlib.Tactic.CrossRefAttribute

/-! # 元の単体図式の core 値因子分解と内 anodyne 延長 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の標準単体が core に属することは、同じ実図式の core への厳密因子分解と同値。 -/
lemma simplex_mem_core_iff_factor {C : SSet.{u}} (n : SimplexCategory)
    (f : stdSimplex.obj n ⟶ C) :
    SSet.yonedaEquiv f ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).obj (Opposite.op n) ↔
      ∃ g : stdSimplex.obj n ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C : SSet.{u}),
        g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).ι = f := by
  constructor
  · intro hf
    refine ⟨SSet.yonedaEquiv.symm ⟨SSet.yonedaEquiv f, hf⟩, ?_⟩
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    rfl
  · rintro ⟨g, rfl⟩
    exact (SSet.yonedaEquiv g).property

/-- 元の W 列の頂点条件は、商の同じ実図式が core を通ることと同値。 -/
lemma weakStringPredicate_iff_factorCore {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) (v : ((ihom (stdSimplex.obj n)).obj B.obj) _⦋0⦌) :
    weakStringPredicate q n v ↔
      ∃ g : stdSimplex.obj n ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj : SSet.{u}),
        g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).ι =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj n) B.obj).symm v ≫ q.hom :=
  by
    unfold weakStringPredicate simplexVertexValue
    exact simplex_mem_core_iff_factor n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj n) B.obj).symm v ≫ q.hom)

/-- 実関手の頂点における W 条件も、元の実関手を保つ同じ厳密因子分解。 -/
lemma weakStringPredicate_functorVertex_iff_factorCore {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : SimplexCategory) (f : stdSimplex.obj n ⟶ B.obj) :
    weakStringPredicate q n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) ↔
      ∃ g : stdSimplex.obj n ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj : SSet.{u}),
        g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).ι = f ≫ q.hom := by
  rw [weakStringPredicate_iff_factorCore]
  change (∃ g, g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).ι =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj n) B.obj).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj n) B.obj) f) ≫ q.hom) ↔ _
  rw [Equiv.symm_apply_apply]

/-- 内 anodyne 包含に沿って、元の quasicategory 値図式を厳密に延長する。 -/
@[kerodon 007E]
lemma exists_extension_of_innerAnodyne {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) (hi : innerAnodyneExtensions i) (f : A ⟶ X) :
    ∃ g : B ⟶ X, i ≫ g = f := by
  have := hi (terminal.from X) (InnerFibration.mem (q := terminal.from X))
  have sq : CommSq f i (terminal.from X) (terminal.from B) := ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 自明 Kan 射影の同じ頂点の二つの持ち上げは、元の全高次 fiber 内で同型。 -/
def vertexIsoOfTrivialKanFibrationEq {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    (x y : E _⦋0⦌) (h : p.app (Opposite.op ⦋0⦌) x = p.app (Opposite.op ⦋0⦌) y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y := by
  let b := p.app (Opposite.op ⦋0⦌) y
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan p b
  let x' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌ := ⟨x, by
    change p.app _ x = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact h⟩
  let y' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌ := ⟨y, by
    change p.app _ y = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (hc.isTerminalVertex x') (hc.isTerminalVertex y'))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)

end SerrePositivity.KST.Fibration
