module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IntervalPathPrecompCylinder
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.HomotopyIsoTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerHom

/-!
概要：同じ全 path を持つ interval 引き戻しへの二射の指定 path 同型を比較する。
方針：全円柱を uncurry の自然性で比較し、両端の等式は端点評価から明示する。
規約：入力 fiber の表示が異なってよい。使われ方：元の模型比較の正規化の指定類。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {T X Y X' Y' Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
  (f' : X' ⟶ Z) (g' : Y' ⟶ Z)
  (a : T ⟶ intervalPullback f g) (b : T ⟶ intervalPullback f' g')

/-- 同じ全 path は、異なる入力表示でも同じ指定 path 同型を与える。 -/
lemma intervalPullbackPathIso_precomp_heq_of_path_eq [KanComplex Z]
    (h : a ≫ intervalPullbackPath f g = b ≫ intervalPullbackPath f' g') :
    HEq ((intervalPullbackPathIso f g).precomp a)
      ((intervalPullbackPathIso f' g').precomp b) := by
  have he (j : Fin 2) := congrArg (fun k => k ≫ (intervalEndpointNatTrans j).app Z) h
  have h₀ : a ≫ (intervalPullbackLeft f g ≫ f) =
      b ≫ (intervalPullbackLeft f' g' ≫ f') := by
    simpa only [Category.assoc, intervalPullbackPath_zero] using he 0
  have h₁ : a ≫ (intervalPullbackRight f g ≫ g) =
      b ≫ (intervalPullbackRight f' g' ≫ g') := by
    simpa only [Category.assoc, intervalPullbackPath_one] using he 1
  have hi : functorIsoOfEq ((intervalPullbackPathIso f g).precomp a) h₀ h₁ =
      (intervalPullbackPathIso f' g').precomp b := by
    apply functorIsoOfEq_of_homotopy_h_eq
      (functorHomotopyPrecomp (intervalPullbackPathHomotopy f g) a)
      (functorHomotopyPrecomp (intervalPullbackPathHomotopy f' g') b)
    · rw [functorIso_precomp_hom, intervalPullbackPathIso_hom]
      exact (functorHomotopyPrecomp_hom (intervalPullbackPathHomotopy f g) a).symm
    · rw [functorIso_precomp_hom, intervalPullbackPathIso_hom]
      exact (functorHomotopyPrecomp_hom (intervalPullbackPathHomotopy f' g') b).symm
    · rw [intervalPullbackPathHomotopy_precomp_cylinder,
        intervalPullbackPathHomotopy_precomp_cylinder, h]
  exact (functorIsoOfEq_heq _ h₀ h₁).symm.trans (heq_of_eq hi)

end SerrePositivity.InfinityCategories.F2
