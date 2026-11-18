module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneVertexUnit
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneAdjointSuspension
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# Γ を源とする自然変換の頂点と連結成分を指定単位から計算する

DAG XIII §2.2 の零次数の Ω 比較への前段。元の自然性と実随伴の全単射だけを使い、
指定構造射の頂点での値を厳密に保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open scoped Simplicial
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

/-- 任意の自然変換の全ての頂点の値は、同じ指定単位の頂点の値から厳密に回収できる。 -/
lemma gammaNatural_vertex_value (F : Complex A ⥤ SSet.{u})
    (η : _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A ⟶ F) (M : Complex A)
    (x : (gammaModule A M).obj (Opposite.op ⦋0⦌)) :
    (η.app M).app (Opposite.op ⦋0⦌) x =
      (F.map (gammaVertexUnitHomEquiv A M x)).app (Opposite.op ⦋0⦌)
        ((η.app (𝟙_ (Complex A))).app (Opposite.op ⦋0⦌)
          (gammaUnitSimplex A ⦋0⦌)) := by
  have h := congrArg (fun k => k.app (Opposite.op ⦋0⦌) (gammaUnitSimplex A ⦋0⦌))
    (η.naturality (gammaVertexUnitHomEquiv A M x))
  change (η.app M).app (Opposite.op ⦋0⦌)
    (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map (gammaVertexUnitHomEquiv A M x)).app
      (Opposite.op ⦋0⦌) (gammaUnitSimplex A ⦋0⦌)) = _ at h
  rw [gammaUnit_vertex_generates] at h
  exact h

/-- 特に、指定随伴構造射でも元の圏で同じ頂点の式が成立する。 -/
lemma gammaAdjointSuspension_vertex_value (M : Complex A)
    (x : (gammaModule A M).obj (Opposite.op ⦋0⦌)) :
    ((gammaAdjointSuspension A).app M).right.app (Opposite.op ⦋0⦌) x =
      ((gammaLoopFunctor A).map (gammaVertexUnitHomEquiv A M x)).right.app
        (Opposite.op ⦋0⦌)
        (((gammaAdjointSuspension A).app (𝟙_ (Complex A))).right.app
          (Opposite.op ⦋0⦌) (gammaUnitSimplex A ⦋0⦌)) :=
  gammaNatural_vertex_value A (gammaLoopFunctor A ⋙ PointedSimplicialSet.forget)
    (Functor.whiskerRight (gammaAdjointSuspension A) PointedSimplicialSet.forget) M x

/-- 単位の頂点の値が一致すれば、全複体での連結成分の誘導写像は一致する。 -/
lemma gammaNatural_piZero_eq_of_unit_vertex (F : Complex A ⥤ SSet.{u})
    (η θ : _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A ⟶ F)
    (h : (η.app (𝟙_ (Complex A))).app (Opposite.op ⦋0⦌) (gammaUnitSimplex A ⦋0⦌) =
      (θ.app (𝟙_ (Complex A))).app (Opposite.op ⦋0⦌) (gammaUnitSimplex A ⦋0⦌))
    (M : Complex A) : SSet.mapπ₀ (η.app M) = SSet.mapπ₀ (θ.app M) := by
  funext a
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective a
  change SSet.π₀.mk ((η.app M).app (Opposite.op ⦋0⦌) x) =
    SSet.π₀.mk ((θ.app M).app (Opposite.op ⦋0⦌) x)
  rw [gammaNatural_vertex_value A F η, gammaNatural_vertex_value A F θ, h]

end SerrePositivity.EInfinity.PowerOperation
