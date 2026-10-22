module

public import SerrePositivity.InfinityCategories.F1B.KanLeftHomUniversal

/-!
概要：指定された二つの左 Kan 単位の大域的 Hom 普遍性を合成する。
方針：元の前合成関手の合成式で、同じ合成単位の比較写像を二つの全単射に分解する。
規約：点ごとの Kan 条件の合成はまだ結論しない。両単位の元の類を保持する。
使われ方：既に存在する二つの余極限頂点を、Kan の一意性で比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

variable {A B C D : SSet.{u}}
  (p : A ⟶ B) (q : B ⟶ C) {F : A ⟶ D} {G : B ⟶ D} {H : C ⟶ D}

/-- 元の二つの単位を、元の前合成関手を使って合成した単位。 -/
def leftKanCompositeUnit (β : FunctorHom F (p ≫ G)) (γ : FunctorHom G (q ≫ H)) :
    FunctorHom F ((p ≫ q) ≫ H) :=
  β ≫ (hoFunctor.map ((pre p).app D)).toFunctor.map γ

/-- 同じ合成単位の Hom 比較は、元の二つの Hom 比較の合成。 -/
lemma leftKanCompositeUnit_homMap (β : FunctorHom F (p ≫ G))
    (γ : FunctorHom G (q ≫ H)) (T : C ⟶ D) :
    leftKanHomMap (p ≫ q) (leftKanCompositeUnit p q β γ) T =
      (leftKanHomMap p β (q ≫ T)) ∘ (leftKanHomMap q γ T) := by
  funext η
  dsimp only [leftKanHomMap, leftKanCompositeUnit, Function.comp_apply]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  congr 1
  congr 1
  have hpq : (hoFunctor.map ((pre q).app D)).toFunctor ⋙
      (hoFunctor.map ((pre p).app D)).toFunctor =
      (hoFunctor.map ((pre (p ≫ q)).app D)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map]
  simpa only [CategoryTheory.Functor.comp_map, eqToHom_refl, Category.id_comp,
    Category.comp_id] using (CategoryTheory.Functor.congr_hom hpq η).symm

/-- 大域的 Hom 普遍性は、元の指定単位の合成について保たれる。 -/
lemma leftKanHomUniversal_comp (β : FunctorHom F (p ≫ G)) (γ : FunctorHom G (q ≫ H))
    (hβ : LeftKanHomUniversal p β) (hγ : LeftKanHomUniversal q γ) :
    LeftKanHomUniversal (p ≫ q) (leftKanCompositeUnit p q β γ) := by
  intro T
  rw [leftKanCompositeUnit_homMap]
  exact (hβ (q ≫ T)).comp (hγ T)

end SerrePositivity.InfinityCategories.F2.Presentable
