module

public import SerrePositivity.InfinityCategories.Core.CatInfinity.VertexIsoTerminalEquality
public import SerrePositivity.InfinityCategories.Core.EquivalencePathIso

/-!
概要：trivial Kan fibration の指定比較の固定された制限。
方針：制限先の可縮な fiber へ写して同じ頂点の自己同型を簡約する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：trivial Kan fibration の指定比較の固定された制限。
方針：制限先の可縮な fiber へ写して同じ頂点の自己同型を簡約する。
規約：構成元の指定同型の値を保持する。
使われ方：切断上の指定 path の比較同型の簡約。 -/
lemma trivialKanIso_precomp_isFunctorEqIso {A D E B : SSet.{u}}
    (p : E ⟶ B) [TrivialKanFibration p] (f g : A ⟶ E)
    (h : f ≫ p = g ≫ p) (r : D ⟶ A) (hr : r ≫ f = r ≫ g) :
    IsFunctorEqIso ((functorIsoOfTrivialKanFibration p f g h).precomp r) := by
  let q := (ihom A).map p
  let b := functorVertex (g ≫ p)
  let F := vertexFiber q b
  have hc := vertexFiber_isContractibleKan q b
  have := hc.kanComplex
  let v₀ : F _⦋0⦌ := ⟨functorVertex f, by
    rw [pinchedConstant_zero]
    change functorVertex (f ≫ p) = functorVertex (g ≫ p)
    rw [h]⟩
  let v₁ : F _⦋0⦌ := ⟨functorVertex g, by rw [pinchedConstant_zero]; rfl⟩
  let c := terminalVertexIso (hc.isTerminalVertex v₀) (hc.isTerminalVertex v₁)
  let q' := (ihom D).map p
  let b' := functorVertex (r ≫ g ≫ p)
  let φ := vertexFiberι q b ≫ (pre r).app E
  have hφ : φ ≫ q' = SSet.const b' := by
    change vertexFiberι q b ≫ (pre r).app E ≫ (ihom D).map p = _
    rw [← (pre r).naturality p, ← Category.assoc, vertexFiberι_comp]
    exact SSet.const_comp _ _
  let ψ := vertexFiberLift q' b' φ hφ
  have hc' := vertexFiber_isContractibleKan q' b'
  have := hc'.kanComplex
  have hv : ψ.app (Opposite.op ⦋0⦌) v₀ = ψ.app (Opposite.op ⦋0⦌) v₁ := by
    apply Subtype.ext
    exact congrArg functorVertex hr
  have he := vertexIso_map_eqToIso_of_terminal c ψ hv
    (hc'.isTerminalVertex (ψ.app (Opposite.op ⦋0⦌) v₁))
  have hm := congrArg (fun e ↦ VertexIso.map e (vertexFiberι q' b')) he
  refine ⟨hr, ?_⟩
  change VertexIso.map (VertexIso.map c (vertexFiberι q b)) ((pre r).app E) = functorEqIso hr
  rw [vertexIso_map_comp]
  have hh : HEq (VertexIso.map c φ)
      (VertexIso.map (VertexIso.map c ψ) (vertexFiberι q' b')) := by
    exact (vertexIso_map_heq c (vertexFiberLift_ι q' b' φ hφ).symm).trans
      (heq_of_eq (vertexIso_map_comp c ψ (vertexFiberι q' b')).symm)
  have hh' := eq_of_heq hh
  rw [hh', hm, functorEqIso_eqToIso]
  simp only [VertexIso.map, eqToIso_map]

end SerrePositivity.InfinityCategories.F2
