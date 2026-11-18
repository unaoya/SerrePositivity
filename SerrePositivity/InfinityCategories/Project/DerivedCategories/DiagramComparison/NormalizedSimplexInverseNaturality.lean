module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.TruncatedDoldKanFunctor
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedHomTargetNaturality

/-!
概要：実Γの全単体の像を正規化標準単体Hom同値で逆に戻す。
方針：既存の標的自然性と同じ同値の両逆射則を使う。
規約：元のΓ・切断・標準単体を保持する既存構成の自然性則。
使われ方：HA 1.2.4、IS-W2 B02の全パラメータ射の成分照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

/-- 元のΓの射を逆転置すると、同じ複体射の後合成となる。 -/
theorem normalizedSimplexHomEquiv_symm_map {K L : Complex A}
    (g : K ⟶ L) (n : SimplexCategory)
    (α : ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj K).obj (Opposite.op n)) :
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A L n).symm
      (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map g).app (Opposite.op n) α) =
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A K n).symm α ≫ g := by
  apply (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A L n).injective
  rw [Equiv.apply_symm_apply]
  have h := _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_postcomp A n
    ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A K n).symm α) g
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
