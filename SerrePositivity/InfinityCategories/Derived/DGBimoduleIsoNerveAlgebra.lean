module
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleStrictNatTransAlgebra
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransNerveHom
/-!
概要：元の双加群射を実 h Fun へ関手的に送り、既存 nerve 同型の恒等・合成・逆を照合する。
方針：元の厳密 dg 自然変換の実 nerve 写像と、同じ指定辺の類の回収を使う。
規約：既存の全関手比較を保持する。使われ方：一般 kernel 比較と結合子の coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalClosed
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (C : Type (max (u + 1) v)) [DGCategory R C]
/-- 元の双加群と全 Hom 自然な閉射を、同じ dg 関手と厳密変換の圏へ送る。 -/
def dgBimoduleStrictFunctor : BimoduleCategory R E C ⥤ DGStrictFunctor R C (RightModule R E) where
  obj P := ⟨(BimoduleCategory.underlying R E C P).toFunctor⟩
  map f := dgBimoduleMapStrictNatTrans R E C f
  map_id P := dgBimoduleMapStrictNatTrans_id R E C P
  map_comp f g := dgBimoduleMapStrictNatTrans_comp R E C f g
/-- 元の双加群射を、その実 dg nerve 間の関手圏の h の射へ送る関手。 -/
def dgBimoduleFunctorHomFunctor :
    BimoduleCategory R E C ⥤
      hoFunctor.obj ((ihom (dgNerve R C)).obj (dgNerve R (RightModule R E))) :=
  dgBimoduleStrictFunctor R E C ⋙ dgStrictFunctorHomFunctor R C (RightModule R E)
/-- 同じ関手で写した同型は、既存の指定 dg nerve 比較そのもの。 -/
lemma dgBimoduleFunctorHomFunctor_mapIso {P Q : BimoduleCategory R E C} (e : P ≅ Q) :
    (dgBimoduleFunctorHomFunctor R E C).mapIso e = dgBimoduleIsoNerve R E C e := by
  apply Iso.ext
  change dgStrictNatTransNerveHom R C (RightModule R E)
    (dgBimoduleMapStrictNatTrans R E C e.hom) = _
  exact dgStrictNatTransNerveHom_spec R C (RightModule R E) _
/-- 既存の同じ双加群 nerve 比較は恒等を保つ。 -/
lemma dgBimoduleIsoNerve_refl (P : BimoduleCategory R E C) :
    dgBimoduleIsoNerve R E C (Iso.refl P) = Iso.refl _ := by
  rw [← dgBimoduleFunctorHomFunctor_mapIso]
  exact Functor.mapIso_refl _ _
/-- 既存の同じ双加群 nerve 比較は通常順合成を保つ。 -/
lemma dgBimoduleIsoNerve_trans {P Q S : BimoduleCategory R E C} (e : P ≅ Q) (f : Q ≅ S) :
    dgBimoduleIsoNerve R E C (e ≪≫ f) =
      dgBimoduleIsoNerve R E C e ≪≫ dgBimoduleIsoNerve R E C f := by
  rw [← dgBimoduleFunctorHomFunctor_mapIso, ← dgBimoduleFunctorHomFunctor_mapIso,
    ← dgBimoduleFunctorHomFunctor_mapIso]
  exact Functor.mapIso_trans _ _ _
/-- 既存の同じ双加群 nerve 比較は指定逆同型を保つ。 -/
lemma dgBimoduleIsoNerve_symm {P Q : BimoduleCategory R E C} (e : P ≅ Q) :
    dgBimoduleIsoNerve R E C e.symm = (dgBimoduleIsoNerve R E C e).symm := by
  rw [← dgBimoduleFunctorHomFunctor_mapIso, ← dgBimoduleFunctorHomFunctor_mapIso]
  exact Functor.mapIso_symm _ _
end SerrePositivity.InfinityCategories
