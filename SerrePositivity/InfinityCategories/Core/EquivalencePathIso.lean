module

public import SerrePositivity.InfinityCategories.Core.EquivalencePathLifting
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-!
概要：点ごとに可逆なホモトピーから関手の同型を構成する。
方針：可逆 path の始点評価の可縮な fiber で二つの持ち上げを比較する。
規約：ホモトピーの向きは標準区間を第一因子に置く。
使われ方：Kerodon §4.5.3、Theorem 4.8.4.1 の同値の path。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：trivial Kan fibration の同じ射の二つの持ち上げは関手単体集合で同型。
方針：内部 Hom による後合成の可縮な fiber に含め、終対象の一意性を使う。
規約：射の後合成が厳密に等しいことを仮定する。
使われ方：Kerodon §4.5.3 の path の持ち上げの比較。 -/
noncomputable def functorIsoOfTrivialKanFibration {A E B : SSet.{u}}
    (p : E ⟶ B) [TrivialKanFibration p] (f g : A ⟶ E) (h : f ≫ p = g ≫ p) :
    FunctorIso f g := by
  let q := (ihom A).map p
  let b := functorVertex (g ≫ p)
  have hc := vertexFiber_isContractibleKan q b
  have := hc.kanComplex
  let v₀ : (vertexFiber q b) _⦋0⦌ := ⟨functorVertex f, by
    rw [pinchedConstant_zero]
    change functorVertex (f ≫ p) = functorVertex (g ≫ p)
    rw [h]⟩
  let v₁ : (vertexFiber q b) _⦋0⦌ := ⟨functorVertex g, by
    rw [pinchedConstant_zero]
    rfl⟩
  exact VertexIso.map
    (terminalVertexIso (hc.isTerminalVertex v₀) (hc.isTerminalVertex v₁)) (vertexFiberι q b)

/-- 概要：全ての垂直辺が可逆なホモトピーの両端は関手単体集合で同型。
方針：ホモトピーを可逆 path へ持ち上げ、同じ始点を持つ定値 path と比較する。
規約：始域に quasicategory 性は不要、標的は quasicategory。
使われ方：Kerodon §4.5.3 の点ごとの同値から関手の同値への構成。 -/
noncomputable def functorIsoOfEquivalenceHomotopy {A Y : SSet.{u}} [Quasicategory Y]
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y)
    (hH : ∀ x : A _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))) :
    FunctorIso (prismEndpoint 0 A ≫ H) (prismEndpoint 1 A ≫ H) := by
  have hv : ∀ x, IsEquivalencePathVertex ((curry H).app (Opposite.op ⦋0⦌) x) := by
    intro x
    unfold IsEquivalencePathVertex
    rw [intervalFunctorVertexEdge_curry]
    exact hH x
  let a := fullSubcomplexLift IsEquivalencePathVertex (curry H) hv
  let f := prismEndpoint 0 A ≫ H
  let b := f ≫ equivalencePathRefl Y
  have ha : a ≫ equivalencePathι Y = curry H := fullSubcomplexLift_ι _ _ _
  have hb : b ≫ equivalencePathEndpoint Y 0 = f := by
    rw [Category.assoc, equivalencePathRefl_endpoint, Category.comp_id]
  have hab : a ≫ equivalencePathEndpoint Y 0 = b ≫ equivalencePathEndpoint Y 0 := by
    rw [hb]
    change a ≫ equivalencePathι Y ≫ evaluateFunctorAt _ = _
    rw [← Category.assoc, ha, curry_evaluateFunctorAt_interval]
  let e := FunctorIso.postcomp
    (functorIsoOfTrivialKanFibration (equivalencePathEndpoint Y 0) a b hab).symm
    (equivalencePathEndpoint Y 1)
  have ha₁ : a ≫ equivalencePathEndpoint Y 1 = prismEndpoint 1 A ≫ H := by
    change a ≫ equivalencePathι Y ≫ evaluateFunctorAt _ = _
    rw [← Category.assoc, ha, curry_evaluateFunctorAt_interval]
  have hb₁ : b ≫ equivalencePathEndpoint Y 1 = f := by
    rw [Category.assoc, equivalencePathRefl_endpoint, Category.comp_id]
  rw [hb₁, ha₁] at e
  exact e

end SerrePositivity.InfinityCategories
