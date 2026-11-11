module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedCoveredArrowRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaClosedPerfectHomotopyCover
/-!
概要：共通提示上の射影的 perfect 端点の閉射を、選択 seed 間の閉射へ移す。
方針：端点のホモトピー被覆と商関手の充満性から閉射を選び、実延長の H⁰ 作用で輸送する。
規約：端点比較と第一辺の可換式を保持し、共通提示そのものの存在は仮定する。
使われ方：c′ の代表加群閉射の精密化を、既存の cone 被覆判定へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type u) [DGCategory R D] (κ : Cardinal.{u})

lemma dgKappaPresentedClosedArrowRefinement_of_perfect_source
    (hκ : κ ≠ 0) (c : DGCategoryPresentationCode R κ)
    (L : DGFunctor R (c.Objects R κ) D)
    (A B : ModuleCategory R (c.Objects R κ))
    (hA : moduleHomotopicallyProjective R (c.Objects R κ) A)
    (hB : moduleHomotopicallyProjective R (c.Objects R κ) B)
    (pA : modulePerfect R (c.Objects R κ) ((moduleToDerived R (c.Objects R κ)).obj A))
    (pB : modulePerfect R (c.Objects R κ) ((moduleToDerived R (c.Objects R κ)).obj B))
    (g : A ⟶ B) {M N : ModuleCategory R D} (f : M ⟶ N)
    (eA : (moduleToHomotopy R D).obj ((dgModuleExtension R (c.Objects R κ) D L).onClosed.obj A) ≅
      (moduleToHomotopy R D).obj M)
    (eB : (moduleToHomotopy R D).obj ((dgModuleExtension R (c.Objects R κ) D L).onClosed.obj B) ≅
      (moduleToHomotopy R D).obj N)
    (comm : (moduleToHomotopy R D).map ((dgModuleExtension R (c.Objects R κ) D L).onClosed.map g) ≫
      eB.hom = eA.hom ≫ (moduleToHomotopy R D).map f) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedClosedArrowRefinement R D κ f) := by
  obtain ⟨i, ⟨a⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily_perfectHomotopyCovers
    R (c.Objects R κ) κ hκ A hA pA
  obtain ⟨j, ⟨b⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily_perfectHomotopyCovers
    R (c.Objects R κ) κ hκ B hB pB
  let H := moduleToHomotopy R (c.Objects R κ)
  have a : H.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c i) ≅ H.obj A := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt
    exact a
  have b : H.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c j) ≅ H.obj B := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt
    exact b
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedClosedArrowRefinement_of_sourceCovers R D κ c L A B g f
    eA eB comm i j a b

end SerrePositivity.InfinityCategories.Project.DerivedCategories
