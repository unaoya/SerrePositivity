module

public import SerrePositivity.EInfinity.ComplexLimits.KProjectiveDerivedComparison
public import SerrePositivity.InfinityCategories.Derived.SemifreeKProjective

/-!
# 同じ K-projective 導来源と既存 D(R) の同値

概要：実半自由分解の K-projective 部分圏への制限は同じ順方向を持つ ∞ 同値。
方針：既存の半自由 retract の全頂点比較と証明済みの充満忠実性を使う。
規約：D(R) や元の分解を別の模型へ置き換えない。
使われ方：元の cofibrant probe の実写像空間を既存 D(R) へ送る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma kProjectiveDerivedSource_isEssentiallySurjective :
    IsEssentiallySurjective (kProjectiveDerivedSource A) := by
  intro y
  let Y := (Simplex.vertexEquiv (A := A) (D := Semifree A)) y
  let X : KProjectiveComplex A := ⟨Y.val, complexSemifree_isKProjective A Y.property⟩
  refine ⟨Simplex.vertex X, ?_⟩
  have e := (complexSemifreeResolutionRetractIso A).app (Simplex.vertex Y)
  have hy : Simplex.vertex Y = y :=
    (Simplex.vertexEquiv (A := A) (D := Semifree A)).symm_apply_apply y
  have e' : VertexIso ((kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌)
      (Simplex.vertex X)) (Simplex.vertex Y) := e
  exact ⟨e' ≪≫ eqToIso (congrArg HomotopyCategory.mk hy)⟩

lemma kProjectiveDerivedSource_isQCatEquivalence :
    IsQCatEquivalence (kProjectiveDerivedSource A) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (kProjectiveDerivedSource_isFullyFaithful A)
    (kProjectiveDerivedSource_isEssentiallySurjective A)

end SerrePositivity.EInfinity.ComplexLimits
