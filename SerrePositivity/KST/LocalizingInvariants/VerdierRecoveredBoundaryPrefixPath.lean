module

public import SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCylinderSquare
public import SerrePositivity.KST.LocalizingInvariants.FractionFamilyComparisonIso
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation

/-!
概要：回収済みの実前段と元の実分数評価の比較辺は、同じ全共有経路を保持する。
方針：実正方形そのものを円柱へ移し、元の終端分母一次単体と共有始点で照合する。
規約：二胞体を Hom 類へ落として選び直さず、元の全比較辺をそのまま使う。
使われ方：境界円柱の全前段比較と全次辺比較を相対 attachment へ直接貼り合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}} {S : K.Subcomplex}
  {a : S.toSSet ⟶ verdierDenominatorSpanFamily i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z}
  {f : K ⟶ intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}

/-- 回収した同じ実境界円柱に元の分数評価正方形を適用した、指定された全比較円柱。 -/
def VerdierFiniteMappingCoconeRecovery.boundaryFractionHomotopy
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :=
  spanSquareFamilyHomotopy (r.boundary.h ≫ verdierSpanEvaluationSquare h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)

lemma VerdierFiniteMappingCoconeRecovery.boundaryFractionHomotopy_source
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ r.boundaryFractionHomotopy.h =
      snd Δ[0] Δ[1] ≫
        internalHomFlipHomEquiv (S.toSSet ⊗ (Δ[1] : SSet.{u})) Δ[1] B.obj
          (verdierSpanFamilyDenominatorArrow i
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z r.boundary.h) ≫
          (ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom := by
  rw [boundaryFractionHomotopy, spanSquareFamilyHomotopy_source]
  simp only [Category.assoc]
  rw [verdierSpanEvaluationSquare_left]
  change snd Δ[0] Δ[1] ≫
    internalHomFlipHomEquiv (S.toSSet ⊗ (Δ[1] : SSet.{u})) Δ[1] C.obj
      (verdierSpanFamilyDenominatorArrow i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z r.boundary.h ≫
        (ihom (Δ[1] : SSet.{u})).map q.hom) = _
  rw [spanInternalHomFlip_post q.hom]

/-- 指定された同じ分数評価円柱の比較辺自体が可逆。 -/
lemma VerdierFiniteMappingCoconeRecovery.boundaryFractionComparison_isInvertible
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    IsInvertibleEdge
      (functorEdgeOfSimplicialHomotopy r.boundaryFractionHomotopy) := by
  have hi := fractionFamilyComparison_isInvertible q.hom (weakEquivalences i) h.inverts
    (r.boundary.h ≫ verdierDenominatorSpanCanonicalComparison i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
      fixedMarkedSpanInclusion B.obj (weakEquivalences i)
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
  apply (isInvertibleEdge_congr
    (e := functorEdgeOfSimplicialHomotopy r.boundaryFractionHomotopy)
    (f := functorEdgeOfSimplicialHomotopy (spanSquareFamilyHomotopy
      ((r.boundary.h ≫ verdierDenominatorSpanCanonicalComparison i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
        fixedMarkedSpanInclusion B.obj (weakEquivalences i)
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) ≫
        fractionEvaluationSquare q.hom (weakEquivalences i) h.inverts))) ?_).mpr hi
  rfl

/-- 元の実前段左辺と同じ分数比較辺は、共有点上の全経路として厳密に一致する。 -/
lemma VerdierFiniteMappingCoconeRecovery.boundaryFractionComparison_sharedSource
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    SSet.yonedaEquiv.symm
        (functorEdgeOfSimplicialHomotopy r.boundaryFractionHomotopy).edge ≫
        (pre (stdSimplex.δ (1 : Fin 2))).app
          ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj C.obj) =
      SSet.yonedaEquiv.symm
        (((squareLeftArrow r.cylinderSquare).map ((truncation 2).map
          ((ihom (Δ[n] : SSet.{u})).map
            ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom)))).edge) ≫
        (pre (simplexLastPoint n)).app ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj C.obj) := by
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry r.boundaryFractionHomotopy.h)) ≫ _ = _
  rw [Equiv.symm_apply_apply, curry_pre_app, r.boundaryFractionHomotopy_source]
  apply (cancel_mono
    (pointFunctorEvaluationIso ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj C.obj)).hom).mp
  change curry (snd (Δ[0] : SSet.{u}) Δ[1] ≫ _ ≫ _) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
    (_ ≫ (pre (simplexLastPoint n)).app _) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  rw [curry_evaluateFunctorAt_vertex, Category.assoc, stable_pre_evaluateFunctorAt]
  simp only [← Category.assoc, lift_snd, Category.id_comp]
  have hp : (simplexLastPoint n).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = stdSimplex.obj₀Equiv.symm (Fin.last n) := by
    have h₀ : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
    rw [h₀, ← SSet.yonedaEquiv_comp, Category.id_comp]
    exact Equiv.apply_symm_apply _ _
  rw [hp]
  rw [SSet.yonedaEquiv_symm_comp]
  change _ = SSet.yonedaEquiv.symm
    ((evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n))).app (Opposite.op ⦋1⦌)
      (((squareLeftArrow r.cylinderSquare).map ((truncation 2).map
        ((ihom (Δ[n] : SSet.{u})).map
          ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom)))).edge))
  rw [r.cylinderSquare_left_quotient_terminal, Equiv.symm_apply_apply]

end SerrePositivity.KST.LocalizingInvariants
