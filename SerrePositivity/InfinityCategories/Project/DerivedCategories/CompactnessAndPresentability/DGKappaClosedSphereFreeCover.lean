module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereFreeCover
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaClosedProjectiveFamily
/-!
概要：κ未満の任意シフト自由直和を、閉射影的代表族の同じ seed で被覆する。
方針：初期切片への再添字による自由代表を閉包の基底へ入れる。
規約：実加群の同型を供給し、射の共通源精密化は別に行う。
使われ方：c′ の自由行列精密化の端点を既存の選択 seed へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u})

lemma dgKappaClosedProjectiveFamily_sphereFreeCovers (hκ : κ ≠ 0)
    (I : Type u) (object : I → D) (degree : I → ℤ) (hI : Cardinal.mk I < κ) :
    ∃ i : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R D κ).1,
      Nonempty ((((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R D κ).2 i).val) ≅
        ∐ (fun j => freeSphere R D (object j) (degree j))) := by
  obtain ⟨i, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule_covers R D I object degree hI
  haveI : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType hκ
  obtain ⟨j, hj⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_base R D
    (T := κ.ord.ToType) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveBaseFamily R D κ) (Sum.inl i)
  refine ⟨j, ?_⟩
  change Nonempty ((((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily R D (T := κ.ord.ToType)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveBaseFamily R D κ)).2 j).val) ≅
      ∐ (fun j => freeSphere R D (object j) (degree j)))
  rw [hj]
  exact ⟨e⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
