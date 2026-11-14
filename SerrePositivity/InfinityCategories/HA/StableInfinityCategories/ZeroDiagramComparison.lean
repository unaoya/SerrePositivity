module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.Pointed
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorTerminal
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence

/-! # 零対象を値とする図式の整合的な同型

概要：各頂点で零対象となる二つの図式は、関手 ∞ 圏の可逆二胞体で比較できる。
方針：点ごとの終対象性から関手頂点の終対象性を使い、終対象の一意性で比較する。
規約：単なる成分ごとの同型の族ではない。使われ方：β3 の零化の自然同型。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 零対象を値とする二図式の、関手 ∞ 圏での同型。 -/
def zeroDiagramFunctorIso {K X : SSet.{u}} [Quasicategory X] (f g : K ⟶ X)
    (hf : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (f.app _ k))
    (hg : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (g.app _ k)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise f (fun k => (hf k).2))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise g (fun k => (hg k).2))

/-- 零図式の間の可逆二胞体は関手ホモトピー圏で一意。 -/
lemma zeroDiagramFunctorIso_unique {K X : SSet.{u}} [Quasicategory X] (f g : K ⟶ X)
    (hg : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (g.app _ k)) (e e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) : e = e' := by
  apply Iso.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise g (fun k => (hg k).2)).isTerminalHo.hom_ext _ _

/-- 定値関手の頂点は、指定した頂点そのもの。 -/
lemma zeroDiagram_const_vertex {K X : SSet.{u}} (z : X _⦋0⦌) (k : K _⦋0⦌) :
    (SSet.const z).app (Opposite.op ⦋0⦌) k = z := by
  change X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op z = z
  have he : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := by
    ext i : 3
    exact Subsingleton.elim (0 : Fin 1) (i : Fin 1)
  rw [he]
  change X.map (𝟙 (Opposite.op ⦋0⦌)) z = z
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- 零対象を値とする図式は、選ばれた零頂点の定値図式と整合的に同型。 -/
def zeroDiagramConstantIso {K X : SSet.{u}} [Quasicategory X] (f : K ⟶ X)
    (hf : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (f.app _ k)) (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f (SSet.const z.vertex) :=
  zeroDiagramFunctorIso f (SSet.const z.vertex) hf (fun k => by
    rw [zeroDiagram_const_vertex]
    exact z.isZero)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
