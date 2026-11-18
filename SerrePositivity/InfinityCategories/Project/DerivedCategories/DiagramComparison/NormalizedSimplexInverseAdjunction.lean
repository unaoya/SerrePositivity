module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LiftedStandardSimplexHomEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeNegativeStandardHomEvaluation

/-!
概要：正規化標準単体Homの逆同値を同じ自由随伴に同定し全生成元を評価する。
方針：同じ恒等単体評価と両逆射則を使い、実標準Homの全次数評価へ戻す。
規約：指定Γ・標準単体・宇宙同型を変更しない既存構成の法則。
使われ方：HA 1.2.4、IS-W2 B02のA09側の全パラメータとAW切断の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory AlgebraicTopology HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 同じ正規化標準単体Homの逆射は指定自由随伴の逆射である。 -/
theorem normalizedSimplexHomEquiv_symm_freeAdjunction (H : Complex A)
    (n : SimplexCategory)
    (α : ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj H).obj (Opposite.op n)) :
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A H n).symm α =
      ((freeNegativeChainsAdjunction A).homEquiv
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)) H).symm
        ((liftedStandardSimplexHomIso ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj H)).inv.app
          (Opposite.op n) α) := by
  apply (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A H n).injective
  rw [Equiv.apply_symm_apply]
  have h := normalizedSimplexHomEquiv_via_freeAdjunction A H n
    (((freeNegativeChainsAdjunction A).homEquiv
      ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)) H).symm
        ((liftedStandardSimplexHomIso ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj H)).inv.app
          (Opposite.op n) α))
  rw [Equiv.apply_symm_apply] at h
  have hi := ConcreteCategory.congr_hom
    (Iso.inv_hom_id_app (liftedStandardSimplexHomIso
      ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj H)) (Opposite.op n)) α
  exact hi.symm.trans h

/-- 同じ標準単体Hom同型の逆射則を任意の台単体集合で固定する。 -/
theorem liftedStandardSimplexHomIso_inv_hom_apply (Z : SSet.{u}) (m : SimplexCategory)
    (t : (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m) ⟶ Z) :
    (liftedStandardSimplexHomIso Z).inv.app (Opposite.op m)
      ((liftedStandardSimplexHomIso Z).hom.app (Opposite.op m) t) = t := by
  exact ConcreteCategory.congr_hom
    (Iso.hom_inv_id_app (liftedStandardSimplexHomIso Z) (Opposite.op m)) t

/-- 元の実標準Homから来る標準単体パラメータの逆同値を全生成元で評価する。 -/
theorem normalizedSimplexHomEquiv_symm_standard_generator
    {D : Type v} [DGCategory A D] (x y : D) (m : SimplexCategory)
    (f : (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m) ⟶
      standardHomSpace (R := A) x y) (n : ℕ)
    (s : ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)).obj
      (Opposite.op ⦋n⦌)) :
    ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A (homObject A D x y) m).symm
      ((liftedStandardSimplexHomIso
        ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj (homObject A D x y))).hom.app (Opposite.op m)
          (f ≫ standardDoldKanSpaceMap x y))).f (-(n : ℤ))
            (freeNegativeGenerator
              ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) n s) =
      standardTopEval (R := A) x y n (f.app _ s) := by
  rw [normalizedSimplexHomEquiv_symm_freeAdjunction]
  rw [liftedStandardSimplexHomIso_inv_hom_apply]

  exact freeNegativeStandardHom_generator_eval
    ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) x y f n s

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
