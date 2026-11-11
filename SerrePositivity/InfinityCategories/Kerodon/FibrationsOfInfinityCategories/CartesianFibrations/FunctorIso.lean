module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Functor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleCartesian
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHomotopyEdges
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.HomotopyBoundaryExtension

/-!
概要：関手の同型による cocartesian 辺の保存条件の不変性。
方針：可逆な成分を持つホモトピーの正方形に合成と消去を適用する。
規約：始域の quasicategory 性や底上の同型という追加仮定を課さない。
使われ方：cocartesian 相対関手の全部分複体への制限同値の移送。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 関手の同型は、各辺の像が cocartesian であるという条件を順方向へ移す。 -/
lemma isCocartesianEdge_of_functorIso {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [InnerFibration p]
    {f g : A ⟶ E} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e : A _⦋1⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (f.app (Opposite.op ⦋1⦌) e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (g.app (Opposite.op ⦋1⦌) e) := by
  let H := h.simplicialHomotopy
  let K : (Δ[1] : SSet.{u}) ⊗ A ⟶ E := (β_ _ _).hom ≫ H.h
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ K = f := by
    dsimp only [K]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding, H.h₀]
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ K = g := by
    dsimp only [K]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding, H.h₁]
  have hv (x : A _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p
      (K.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)) := by
    have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible
      h.edge h.edge_isInvertible x
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_isInvertibleEdge p
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated hi
    convert hc using 1
    change K.app _ (_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) =
      H.h.app _ ((Truncated.Edge.id (X := (truncation 2).obj A) x).edge,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
    change H.h.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1, _) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
    congr 1
    apply Prod.ext
    · rfl
    apply stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianHomotopy_targetEdge p K (SSet.yonedaEquiv.symm e)
    (by rw [h₀, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]; exact he) hv
  rwa [h₁, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hc

/-- 各辺の像の cocartesian 性は関手の同型で不変。 -/
lemma isCocartesianEdge_iff_of_functorIso {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [InnerFibration p]
    {f g : A ⟶ E} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e : A _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (f.app (Opposite.op ⦋1⦌) e) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (g.app (Opposite.op ⦋1⦌) e) :=
  ⟨isCocartesianEdge_of_functorIso p h e, isCocartesianEdge_of_functorIso p h.symm e⟩

/-- 全 cocartesian 辺の保存条件は関手の同型で不変。 -/
lemma preservesCocartesianEdges_iff_of_functorIso {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : A ⟶ B) (q : E ⟶ B) [InnerFibration q]
    {f g : A ⟶ E} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges p q f ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges p q g := by
  constructor <;> intro hf e he
  · exact (isCocartesianEdge_iff_of_functorIso q h e).mp (hf e he)
  · exact (isCocartesianEdge_iff_of_functorIso q h e).mpr (hf e he)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
