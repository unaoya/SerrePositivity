module

public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyIsoPostcomp

/-!
概要：後合成した同型の射の Arrow の等式を、さらに同じ射で後合成する。
方針：h Fun の後合成関手の Arrow への作用と、二段階の関手法則を使う。
規約：異なる端点表示を許す。使われ方：初期 Hom の底から通常の Hom 表示への移行。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 同じ後合成後の Arrow の等式は、さらに後合成した同じ像でも保たれる。 -/
lemma functorIso_postcomp_hom_arrow_map {T E B C : SSet.{u}} {a b c d : T ⟶ E}
    (I : FunctorIso a b) (J : FunctorIso c d) (p : E ⟶ B) (q : B ⟶ C)
    (h : Arrow.mk (FunctorIso.postcomp I p).hom = Arrow.mk (FunctorIso.postcomp J p).hom) :
    Arrow.mk (FunctorIso.postcomp I (p ≫ q)).hom =
      Arrow.mk (FunctorIso.postcomp J (p ≫ q)).hom := by
  have hq := congrArg (hoFunctor.map ((ihom T).map q)).toFunctor.mapArrow.obj h
  rw [functorIso_postcomp_hom, functorIso_postcomp_hom] at hq
  let F := (hoFunctor.map ((ihom T).map (p ≫ q))).toFunctor
  have hF : F = (hoFunctor.map ((ihom T).map p)).toFunctor ⋙
      (hoFunctor.map ((ihom T).map q)).toFunctor := by
    change (hoFunctor.map ((ihom T).map (p ≫ q))).toFunctor = _
    rw [(ihom T).map_comp p q, hoFunctor.map_comp, Cat.Hom.comp_toFunctor]
  rw [functorIso_postcomp_hom, functorIso_postcomp_hom]
  change F.mapArrow.obj (Arrow.mk I.hom) = F.mapArrow.obj (Arrow.mk J.hom)
  rw [hF]
  simpa only [Functor.mapArrow_obj, Functor.comp_map, Arrow.mk_hom] using hq

end SerrePositivity.InfinityCategories.HomotopyLimits
