module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexCoslicePointedFamily
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedCoherentCosliceNormalization
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedLiftFaces

/-!
概要：元の全 Space 単体上で、反転 Hom 全体の族を実 pointed space に構成する。
方針：元の coslice 前合成を一点頂点の既存の等式で正規化する。
規約：元の全図式・全係数・全 pointed 単体を保持する。
使われ方：指定三角形の全 Hom 比較を同じ pointed 族へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌)

/-- 元の全標準単体の上で、反転 Hom 全体に依存する実 pointed 族。 -/
def spaceSimplexPointedFamily : (Δ[n] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom pointKanObject (s.obj ⟨ULift.up 0⟩)).op ⟶ PointedSpaceInfinity.{u} :=
  spaceSimplexCoslicePointedFamily s ≫ pointedCoherentCosliceIso.hom

/-- 同じ全 Hom 族の射影は、係数に依存せず元の全図式に厳密に等しい。 -/
lemma spaceSimplexPointedFamily_projection :
    spaceSimplexPointedFamily s ≫ pointedSpaceProjection =
      fst _ _ ≫ SSet.yonedaEquiv.symm s := by
  rw [spaceSimplexPointedFamily, Category.assoc, pointedCoherentCosliceIso_projection,
    spaceSimplexCoslicePointedFamily_projection]

/-- 同じ対角係数の値は、元の pointed 持ち上げと全単体として厳密に一致する。 -/
lemma spaceSimplexPointedFamily_diagonal
    (p : (Δ[n] : SSet.{u}) ⟶ (SimplicialCategory.sHom pointKanObject
      (s.obj ⟨ULift.up 0⟩)).op) :
    (spaceSimplexPointedFamily s).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (𝟙 Δ[n]), ULift.up (SSet.yonedaEquiv p)) =
        spaceSimplexPointedLift s p := by
  apply Subtype.ext
  apply (cancel_epi (leftPointStdSimplexIso n).inv).mp
  apply SSet.yonedaEquiv.injective
  change SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
    (pointedCoherentCosliceIso.hom.app (Opposite.op ⦋n⦌)
      ((spaceSimplexCoslicePointedFamily s).app (Opposite.op ⦋n⦌)
        (SSet.yonedaEquiv (𝟙 Δ[n]), ULift.up (SSet.yonedaEquiv p)))).val) = _
  rw [pointedCoherentCosliceIso_app_val]
  exact (spaceSimplexCoslicePointedFamily_diagonal_coordinates s p).trans
    (spaceSimplexPointedLift_coordinates s p).symm

end SerrePositivity.InfinityCategories.F2
