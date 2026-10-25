module
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedSourceConeRefinement
public import SerrePositivity.InfinityCategories.Derived.DGKappaClosedPerfectHomotopyCover
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
namespace SerrePositivity.InfinityCategories
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
    Nonempty (DGKappaPresentedClosedArrowRefinement R D κ f) := by
  obtain ⟨i, ⟨a⟩⟩ := dgKappaClosedProjectiveFamily_perfectHomotopyCovers
    R (c.Objects R κ) κ hκ A hA pA
  obtain ⟨j, ⟨b⟩⟩ := dgKappaClosedProjectiveFamily_perfectHomotopyCovers
    R (c.Objects R κ) κ hκ B hB pB
  let H := moduleToHomotopy R (c.Objects R κ)
  have a : H.obj (dgKappaPresentedSeedAt R κ c i) ≅ H.obj A := by
    unfold dgKappaPresentedSeedAt
    exact a
  have b : H.obj (dgKappaPresentedSeedAt R κ c j) ≅ H.obj B := by
    unfold dgKappaPresentedSeedAt
    exact b
  obtain ⟨g', hg'⟩ := H.map_surjective (a.hom ≫ H.map g ≫ b.inv)
  let E := dgModuleExtension R (c.Objects R κ) D L
  let J : ModuleHomotopyCategory R (c.Objects R κ) ⥤ ModuleHomotopyCategory R D := E.onHomotopy
  refine ⟨⟨c, L, i, j, g', J.mapIso a ≪≫ eA,
    J.mapIso b ≪≫ eB, ?_⟩⟩
  change J.map (H.map g') ≫ (J.map b.hom ≫ eB.hom) =
    (J.map a.hom ≫ eA.hom) ≫ (moduleToHomotopy R D).map f
  rw [hg']
  have hb : J.map b.inv ≫ J.map b.hom = 𝟙 _ := by
    rw [← Functor.map_comp, b.inv_hom_id, CategoryTheory.Functor.map_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (J.map b.inv), hb, Category.id_comp]
  change J.map a.hom ≫ ((moduleToHomotopy R D).map (E.onClosed.map g) ≫ eB.hom) = _
  rw [comm]

end SerrePositivity.InfinityCategories
