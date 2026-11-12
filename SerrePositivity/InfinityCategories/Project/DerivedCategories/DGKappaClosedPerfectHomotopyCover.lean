module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaClosedProjectiveFamily
/-!
概要：射影的 perfect 加群を閉代表族の同じ実対象でホモトピー同型まで被覆する。
方針：主導来圏での代表被覆を、射影的 perfect 比較の完全忠実性で戻す。
規約：導来同型を実加群の厳密同型とみなさず、ホモトピー圏の同型を保持する。
使われ方：c′ の同時精密化で、perfect seed の延長像を新しい共通源の seed へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u})

lemma dgKappaPerfectRepresentative_homotopyCovers (M : ModuleCategory R D)
    (hp : moduleHomotopicallyProjective R D M)
    (hM : modulePerfect R D ((moduleToDerived R D).obj M)) :
    ∃ i : SmallModel.{u} (PerfectModuleCategoryOver R D Set.univ),
      Nonempty ((moduleToHomotopy R D).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPerfectRepresentative R D i) ≅
        (moduleToHomotopy R D).obj M) := by
  obtain ⟨i, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPerfectRepresentative_covers R D M hM
  let A : PerfectDGModule R D := perfectDGModuleRepresentative R D Set.univ i
  let B : PerfectDGModule R D := ⟨ForgetEnrichment.to (Complex R) M, hp, hM⟩
  let X := (toHomotopy R (PerfectDGModule R D)).obj (ForgetEnrichment.of (Complex R) A)
  let Y := (toHomotopy R (PerfectDGModule R D)).obj (ForgetEnrichment.of (Complex R) B)
  let e' : (perfectDGModuleToDerived R D Set.univ).obj X ≅
      (perfectDGModuleToDerived R D Set.univ).obj Y :=
    (moduleToHomotopyDerivedIso R D).app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPerfectRepresentative R D i) ≪≫ e ≪≫
      ((moduleToHomotopyDerivedIso R D).app M).symm
  let h := Functor.FullyFaithful.ofFullyFaithful (perfectDGModuleToDerived R D Set.univ)
  exact ⟨i, ⟨(perfectDGModuleInclusion R D Set.univ).onHomotopy.mapIso
    (h.preimageIso e')⟩⟩

lemma dgKappaClosedProjectiveFamily_perfectHomotopyCovers (hκ : κ ≠ 0)
    (M : ModuleCategory R D) (hp : moduleHomotopicallyProjective R D M)
    (hM : modulePerfect R D ((moduleToDerived R D).obj M)) :
    ∃ i : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R D κ).1,
      Nonempty ((moduleToHomotopy R D).obj
        (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R D κ).2 i).val) ≅
        (moduleToHomotopy R D).obj M) := by
  obtain ⟨i, hi⟩ := dgKappaPerfectRepresentative_homotopyCovers R D M hp hM
  haveI : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType hκ
  obtain ⟨j, hj⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily_base R D
    (T := κ.ord.ToType) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveBaseFamily R D κ) (Sum.inr i)
  refine ⟨j, ?_⟩
  change Nonempty ((moduleToHomotopy R D).obj
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily R D (T := κ.ord.ToType)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveBaseFamily R D κ)).2 j).val) ≅
      (moduleToHomotopy R D).obj M)
  rw [hj]
  exact hi

end SerrePositivity.InfinityCategories.Project.DerivedCategories
