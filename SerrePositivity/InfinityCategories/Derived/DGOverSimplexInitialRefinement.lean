module
public import SerrePositivity.InfinityCategories.Derived.RoofPointSliceSimplexInverse
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementAvoidingFaces

/-! # 任意次元の実 over 単体の閉始点細分

概要：元の回収単体を同じ閉射で始点細分し、同じ終点を固定する実 over 単体へ戻す。
方針：正の最終頂点への制限の保存で、零次元も含めて終点固定を照合する。
規約：分母条件は別に証明する。使われ方：高次境界充填の共有面と新 apex の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] {n : ℕ}
variable (a : Δ[0] ⟶ dgNerve A D) (σ : (sliceOver a) _⦋n⦌) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
  ((SSet.yonedaEquiv (roofPointSliceSimplex a σ)).obj 0))

/-- over 単体の元の回収単体を、同じ閉射で始点細分した実単体。 -/
def dgOverSimplexInitialMap : Δ[n + 1] ⟶ dgNerve A D :=
  (SSet.yonedaEquiv (X := dgNerve A D)).symm
    (dgSimplexInitialRefinement A D (SSet.yonedaEquiv (roofPointSliceSimplex a σ)) q s)

/-- 同じ閉始点細分は、元の指定終点を厳密に保つ。 -/
lemma dgOverSimplexInitialMap_fixed :
    SSet.stdSimplex.map (PinchedHom.lastVertex n) ≫ dgOverSimplexInitialMap A D a σ q s = a := by
  unfold dgOverSimplexInitialMap
  rw [SSet.yonedaEquiv_symm_naturality_left]
  have he := dgSimplexInitialRefinement_pullback_avoids_zero A D
    (SSet.yonedaEquiv (roofPointSliceSimplex a σ)) q s (PinchedHom.lastVertex n).toOrderHom
    (fun (i j : Fin 1) _ => Subsingleton.elim i j) (fun i => by
      change Fin.last (n + 1) ≠ 0
      simp)
  change (dgNerve A D).map (PinchedHom.lastVertex n).op
      (dgSimplexInitialRefinement A D (SSet.yonedaEquiv (roofPointSliceSimplex a σ)) q s) =
    (dgNerve A D).map (PinchedHom.lastVertex n).op
      (SSet.yonedaEquiv (roofPointSliceSimplex a σ)) at he
  rw [he, ← SSet.yonedaEquiv_symm_naturality_left, Equiv.symm_apply_apply]
  exact roofPointSliceSimplex_fixed a σ

/-- 全次数・零次元を含む、同じ終点を固定した実 over 単体の閉始点細分。 -/
def dgOverSimplexInitialRefinement : (sliceOver a) _⦋n⦌ :=
  roofPointSliceSimplexOfFixed a (dgOverSimplexInitialMap A D a σ q s)
    (dgOverSimplexInitialMap_fixed A D a σ q s)

/-- over 細分の回収単体は、元の指定回収単体の同じ閉始点細分。 -/
lemma dgOverSimplexInitialRefinement_simplex :
    roofPointSliceSimplex a (dgOverSimplexInitialRefinement A D a σ q s) =
      dgOverSimplexInitialMap A D a σ q s :=
  roofPointSliceSimplexOfFixed_simplex a _ _

end SerrePositivity.InfinityCategories
