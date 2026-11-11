module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedCoveredArrowRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaClosedSphereFreeCover
/-!
概要：共通提示上のκ未満自由直和間の閉射を、選択 seed 間の閉射へ戻す。
方針：自由直和の実 seed 被覆をホモトピー圏へ送り、閉射輸送の一般判定を適用する。
規約：元の閉射全体と実延長の端点比較を保持する。
使われ方：c′ の行有限係数による自由閉射精密化を cone 被覆へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type u) [DGCategory R D] (κ : Cardinal.{u})

lemma dgKappaPresentedClosedArrowRefinement_of_free_source (hκ : κ ≠ 0)
    (c : DGCategoryPresentationCode R κ) (L : DGFunctor R (c.Objects R κ) D)
    {I J : Type u} (x : I → c.Objects R κ) (y : J → c.Objects R κ)
    (n : I → ℤ) (m : J → ℤ) (hI : Cardinal.mk I < κ) (hJ : Cardinal.mk J < κ)
    (g : (∐ fun i => freeSphere R (c.Objects R κ) (x i) (n i)) ⟶
      ∐ fun j => freeSphere R (c.Objects R κ) (y j) (m j))
    {M N : ModuleCategory R D} (f : M ⟶ N)
    (eA : (dgModuleExtension R (c.Objects R κ) D L).onClosed.obj
      (∐ fun i => freeSphere R (c.Objects R κ) (x i) (n i)) ≅ M)
    (eB : (dgModuleExtension R (c.Objects R κ) D L).onClosed.obj
      (∐ fun j => freeSphere R (c.Objects R κ) (y j) (m j)) ≅ N)
    (comm : (dgModuleExtension R (c.Objects R κ) D L).onClosed.map g ≫ eB.hom = eA.hom ≫ f) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedClosedArrowRefinement R D κ f) := by
  obtain ⟨i, ⟨a⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily_sphereFreeCovers
    R (c.Objects R κ) κ hκ I x n hI
  obtain ⟨j, ⟨b⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily_sphereFreeCovers
    R (c.Objects R κ) κ hκ J y m hJ
  have a : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c i ≅ ∐ (fun i => freeSphere R (c.Objects R κ) (x i) (n i)) := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt
    exact a
  have b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c j ≅ ∐ (fun j => freeSphere R (c.Objects R κ) (y j) (m j)) := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt
    exact b
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedClosedArrowRefinement_of_sourceCovers R D κ c L _ _ g f
    ((moduleToHomotopy R D).mapIso eA) ((moduleToHomotopy R D).mapIso eB) _ i j
    ((moduleToHomotopy R (c.Objects R κ)).mapIso a)
    ((moduleToHomotopy R (c.Objects R κ)).mapIso b)
  change (moduleToHomotopy R D).map _ ≫ (moduleToHomotopy R D).map _ =
    (moduleToHomotopy R D).map _ ≫ (moduleToHomotopy R D).map _
  rw [← Functor.map_comp, ← Functor.map_comp, comm]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
