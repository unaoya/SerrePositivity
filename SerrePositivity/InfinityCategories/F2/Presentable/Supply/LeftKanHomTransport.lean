module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.UniversalProperty

/-!
概要：指定左 Kan Hom 比較の全単射性を同型で移す。
方針：元の前合成関手と同型による Hom 全単射で比較写像を共役する。
規約：指定単位を保持する。使われ方：分類模型と元の共変 Hom との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：指定左 Kan Hom 比較の全単射性は標的の同型で移せる。
方針：標的同型の前後合成で比較写像を共役する。
規約：同じ単位を保持する。使われ方：分類された標的から任意の標的への移送。 -/
lemma leftKanHomMap_bijective_of_iso_target {A B X : SSet.{u}} (k : A ⟶ B)
    {F : A ⟶ X} {L G H : B ⟶ X} (β : FunctorHom F (k ≫ L))
    (e : FunctorIso G H) (h : Function.Bijective (leftKanHomMap k β G)) :
    Function.Bijective (leftKanHomMap k β H) := by
  let r := (hoFunctor.map ((pre k).app X)).toFunctor
  have he : leftKanHomMap k β H =
      (Iso.homToEquiv (r.mapIso e)) ∘ (leftKanHomMap k β G) ∘
        (Iso.homToEquiv e).symm := by
    funext η
    change β ≫ r.map η = (β ≫ r.map (η ≫ e.inv)) ≫ r.map e.hom
    calc
      β ≫ r.map η = β ≫ r.map η ≫ r.map (𝟙 _) := by simp
      _ = β ≫ r.map η ≫ r.map (e.inv ≫ e.hom) := by rw [Iso.inv_hom_id]
      _ = (β ≫ r.map (η ≫ e.inv)) ≫ r.map e.hom := by
        simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [he]
  exact (Iso.homToEquiv (r.mapIso e)).bijective.comp
    (h.comp (Iso.homToEquiv e).symm.bijective)

/-- 概要：指定左 Kan 単位の全 Hom 普遍性は始点と延長の同型で移せる。
方針：始点同型の前合成と延長同型の逆の前合成で比較写像を共役する。
規約：指定同型と元の単位を保持する。使われ方：分類模型から元の共変 Hom への移送。 -/
lemma leftKanHomUniversal_iso_unit {A B X : SSet.{u}} (k : A ⟶ B)
    {F F' : A ⟶ X} {L L' : B ⟶ X} (β : FunctorHom F (k ≫ L))
    (hβ : LeftKanHomUniversal k β) (eF : FunctorIso F' F) (eL : FunctorIso L' L) :
    LeftKanHomUniversal k (eF.hom ≫ β ≫ (eL.precomp k).inv) := by
  intro H
  have h := (Iso.homFromEquiv eF.symm
      (Z := HomotopyCategory.mk (functorVertex (k ≫ H)))).bijective.comp
    ((hβ H).comp (Iso.homFromEquiv eL
      (Z := HomotopyCategory.mk (functorVertex H))).bijective)
  convert h using 1
  funext η
  change (eF.hom ≫ β ≫
      (hoFunctor.map ((pre k).app X)).toFunctor.map eL.inv) ≫
        (hoFunctor.map ((pre k).app X)).toFunctor.map η =
    eF.hom ≫ (β ≫ (hoFunctor.map ((pre k).app X)).toFunctor.map (eL.inv ≫ η))
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.F2.Presentable
