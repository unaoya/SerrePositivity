module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.Core.EquivalenceCylinderFunctorIso
/-!
概要：標的への像を固定した実可逆円柱を、相対関手空間内の頂点同型へ移す。
方針：元の全円柱の両端と評価の固定条件を、そのまま実際の射で回収する。
規約：標的の固定 fiber の充填性を追加仮定にしない。
使われ方：指定始点評価の下での全余錐比較の相対反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：標的全図式を固定した実可逆円柱は、相対関手空間内の頂点同型を与える。
方針：可逆区間の両頂点の同型を写す。規約：全射を保持。使われ方：相対反映。 -/
lemma nonempty_relativeFunctorVertexIso_of_equivalenceCylinder
    {A D E : SSet.{u}} (p : D ⟶ E) (a : A ⟶ E)
    (f g : A ⟶ D) (hf : f ≫ p = a) (hg : g ≫ p = a)
    (H : A ⊗ equivalenceInterval ⟶ D)
    (h₀ : equivalenceCylinderEndpoint A false ≫ H = f)
    (h₁ : equivalenceCylinderEndpoint A true ≫ H = g)
    (hH : H ≫ p = fst A equivalenceInterval ≫ a) :
    Nonempty (VertexIso (relativeFunctorVertex p a f hf) (relativeFunctorVertex p a g hg)) := by
  let M := relativeFunctorCurry H hH
  let x : equivalenceInterval.{u} _⦋0⦌ := nerveEquiv.symm (Codiscrete.mk (ULift.up false))
  let y : equivalenceInterval.{u} _⦋0⦌ := nerveEquiv.symm (Codiscrete.mk (ULift.up true))
  have hc := isContractibleKan_codiscreteNerve (ULift.{u} Bool)
  have : KanComplex equivalenceInterval.{u} := hc.kanComplex
  let e := terminalVertexIso (hc.isTerminalVertex x) (hc.isTerminalVertex y)
  have hx : M.app (Opposite.op ⦋0⦌) x = relativeFunctorVertex p a f hf := by
    apply Subtype.ext
    change (curry H).app (Opposite.op ⦋0⦌) x = functorVertex f
    have h := functorVertex_equivalenceCylinderEndpoint_uncurry (curry H) false
    rw [uncurry_curry, h₀] at h
    exact h.symm
  have hy : M.app (Opposite.op ⦋0⦌) y = relativeFunctorVertex p a g hg := by
    apply Subtype.ext
    change (curry H).app (Opposite.op ⦋0⦌) y = functorVertex g
    have h := functorVertex_equivalenceCylinderEndpoint_uncurry (curry H) true
    rw [uncurry_curry, h₁] at h
    exact h.symm
  exact ⟨(eqToIso (congrArg SSet.HomotopyCategory.mk hx)).symm ≪≫
    VertexIso.map e M ≪≫ eqToIso (congrArg SSet.HomotopyCategory.mk hy)⟩
end SerrePositivity.InfinityCategories.F2.Ind
