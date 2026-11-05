module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ProjectiveBarNativeCocone
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeProjectiveEquivalence
public import SerrePositivity.InfinityCategories.F2.Presentable.EquivalenceColimits
public import SerrePositivity.InfinityCategories.Core.ColimitDiagramIso

/-!
概要：任意の小さい coherent 図式は半自由模型で native 余極限を持つ。
方針：射影的模型の bar 余錐を、半自由包含の全写像空間同値で戻す。
規約：元の coherent 図式の全 HA 成分を保持する。
使われ方：strict filtered 比較の native 余極限の存在部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgModuleDerivedInfinityCategory R D)

lemma dgSemifreeCoherent_hasColimit : HasColimit G := by
  let e := (dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose
  let H := G ≫ e.hom
  let c := dgProjectiveBarNativeCocone R D H
  have hc := dgProjectiveBarNativeCocone_isColimit R D H
  have hi := (F2.Presentable.equivalence_isColimitCone_iff e.symm.isQCatEquivalence c).mp hc
  have he : FunctorIso ((G ≫ e.hom) ≫ e.inv) G := by
    simpa only [Category.assoc, Category.comp_id] using e.homInvIso.precomp G
  exact (hasColimit_iff_of_functorIso he).mp ⟨mapJoinCocone e.inv c, hi⟩

end SerrePositivity.InfinityCategories
