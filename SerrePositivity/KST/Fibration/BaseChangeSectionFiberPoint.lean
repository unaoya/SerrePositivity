module
public import SerrePositivity.KST.Fibration.BaseChangeImageSectionValue
public import SerrePositivity.InfinityCategories.F1B.Fibrations.VertexFiberBaseChange

/-! # 同じ切断の初頂点 fiber 点は、元の底変換 fiber 同型で両立する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- fiber の底頂点の等式による点の輸送は、全空間の値を保つ。 -/
theorem vertexFiberPoint_eq_mp_val {E B : SSet.{u}} (p : E ⟶ B)
    {b b' : B _⦋0⦌} (h : b = b') {n : SimplexCategoryᵒᵖ}
    (v : (vertexFiber p b).obj n) :
    (Eq.mp (congrArg (fun z => (vertexFiber p z).obj n) h) v).val = v.val := by
  cases h
  rfl

variable {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B)

local instance : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 像の単体の初頂点は、元の初頂点の底の射による像。 -/
theorem baseChangeImageFirstVertex (c : TransportSimplexCategory D) :
    (transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
      (nerveVertex ((transportSimplexFunctor k).obj c)) =
    k.app (Opposite.op ⦋0⦌)
      ((transportSimplexFirstVertexMap D).app (Opposite.op ⦋0⦌) (nerveVertex c)) :=
  congrArg (fun f : nerve (TransportSimplexCategory D) ⟶ B =>
    f.app (Opposite.op ⦋0⦌) (nerveVertex c)) (transportSimplexFirstVertexMap_naturality k)

/-- 輸送した第一射影切断の初頂点の値は、元の切断の初頂点の第一射影。 -/
theorem baseChangeImageSectionFiberPoint_val (c : TransportSimplexCategory D)
    (v : (relativeFunctorSpace (pullback.snd p k)
      ((transportSimplexDomainFunctor D).obj (Opposite.op c)).hom) _⦋0⦌) :
    (firstVertexSectionFiberPoint p ((transportSimplexFunctor k).obj c)
      (_root_.SerrePositivity.InfinityCategories.Stable.Transport.straighteningBaseChangeImageSectionPoint p k c
        ((relativeFunctorBaseChangeForward p k
          ((transportSimplexDomainFunctor D).obj (Opposite.op c)).hom).app
            (Opposite.op ⦋0⦌) v))).val =
    (pullback.fst p k).app (Opposite.op ⦋0⦌)
      (firstVertexSectionFiberPoint (pullback.snd p k) c v).val := by
  rw [firstVertexSectionFiberPoint_val, firstVertexSectionFiberPoint_val,
    straighteningBaseChangeImageSectionPoint_val]
  exact relativeFunctorBaseChangeForward_apply p k _ v (𝟙 _)
    (stdSimplex.obj₀Equiv.symm (0 : Fin (c.objDown.obj.unop.len + 1)))

/-- 同じ二つの初頂点 fiber 点は、既存の実底変換同型によって厳密に一致する。 -/
theorem baseChangeImageSectionFiberPoint_eq (c : TransportSimplexCategory D)
    (v : (relativeFunctorSpace (pullback.snd p k)
      ((transportSimplexDomainFunctor D).obj (Opposite.op c)).hom) _⦋0⦌) :
    Eq.mp (congrArg (fun b => (vertexFiber p b) _⦋0⦌) (baseChangeImageFirstVertex k c))
      (firstVertexSectionFiberPoint p ((transportSimplexFunctor k).obj c)
        (_root_.SerrePositivity.InfinityCategories.Stable.Transport.straighteningBaseChangeImageSectionPoint p k c
          ((relativeFunctorBaseChangeForward p k
            ((transportSimplexDomainFunctor D).obj (Opposite.op c)).hom).app
              (Opposite.op ⦋0⦌) v))) =
    (cofinalVertexFiberBaseChangeIso p k
      ((transportSimplexFirstVertexMap D).app (Opposite.op ⦋0⦌) (nerveVertex c))).hom.app
        (Opposite.op ⦋0⦌) (firstVertexSectionFiberPoint (pullback.snd p k) c v) := by
  apply Subtype.ext
  exact (vertexFiberPoint_eq_mp_val p (baseChangeImageFirstVertex k c) _).trans
    (baseChangeImageSectionFiberPoint_val p k c v)

end SerrePositivity.KST.Fibration
