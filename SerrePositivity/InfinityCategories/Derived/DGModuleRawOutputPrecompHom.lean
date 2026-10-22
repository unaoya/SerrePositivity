module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedInfinity
public import SerrePositivity.InfinityCategories.Derived.FunctorHomEndpointTransport
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskerMapTransport
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskerHEq
/-!
概要：元の augmentation の自然性を、二射影と同じ指定入力切断の表示へ移す。
方針：同じ全関手射の端点輸送と二段前合成の整合性を保つ。
規約：指定比較と切断・計算上限を変更しない。使われ方：元の κ の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (E K : Type v)
  [DGCategory R E] [Small.{u} E] [DGCategory R K] [Small.{u} K]
local notation "L" => dgModuleResolvedInfinity R (RightModule R K) K
  (DGFunctor.id (RightModule R K))
def dgModuleRawOutputPrecompHom (A : Type (max (u + 1) v)) [DGCategory R A]
    (J : DGFunctor R A (RightModule R E))
    (H0 H1 : DGFunctor R (RightModule R E) (RightModule R K))
    (d : FunctorHom (dgNerve.map H0 ≫ L) (dgNerve.map H1 ≫ L)) :
    FunctorHom (dgNerve.map (J.comp H0) ≫ L) (dgNerve.map (J.comp H1) ≫ L) :=
  functorHomOfMapEq
    (functorHomPrecomp (dgNerve.map H0 ≫ L) (dgNerve.map H1 ≫ L) (dgNerve.map J) d)
    (by simp only [dgNerve.map_comp, Category.assoc])
    (by simp only [dgNerve.map_comp, Category.assoc])
lemma dgModuleRawOutputPrecompHom_heq (A : Type (max (u + 1) v)) [DGCategory R A]
    (J : DGFunctor R A (RightModule R E))
    (H0 H1 : DGFunctor R (RightModule R E) (RightModule R K))
    (d : FunctorHom (dgNerve.map H0 ≫ L) (dgNerve.map H1 ≫ L)) :
    HEq (dgModuleRawOutputPrecompHom R E K A J H0 H1 d)
      (functorHomPrecomp (dgNerve.map H0 ≫ L) (dgNerve.map H1 ≫ L) (dgNerve.map J) d) :=
  functorHomOfMapEq_heq _ _ _
lemma dgModuleRawOutputPrecompHom_precomp_heq
    (A B : Type (max (u + 1) v)) [DGCategory R A] [DGCategory R B]
    (J : DGFunctor R A (RightModule R E)) (G : DGFunctor R B A)
    (H0 H1 : DGFunctor R (RightModule R E) (RightModule R K))
    (d : FunctorHom (dgNerve.map H0 ≫ L) (dgNerve.map H1 ≫ L)) :
    HEq (functorHomPrecomp (dgNerve.map (J.comp H0) ≫ L)
      (dgNerve.map (J.comp H1) ≫ L) (dgNerve.map G)
      (dgModuleRawOutputPrecompHom R E K A J H0 H1 d))
      (functorHomPrecomp (dgNerve.map H0 ≫ L) (dgNerve.map H1 ≫ L)
        (dgNerve.map (G.comp J)) d) := by
  have h0 : dgNerve.map (J.comp H0) ≫ L = dgNerve.map J ≫ (dgNerve.map H0 ≫ L) := by
    simp only [dgNerve.map_comp, Category.assoc]
  have h1 : dgNerve.map (J.comp H1) ≫ L = dgNerve.map J ≫ (dgNerve.map H1 ≫ L) := by
    simp only [dgNerve.map_comp, Category.assoc]
  have ha := functorHom_precomp_heq
    (dgModuleRawOutputPrecompHom R E K A J H0 H1 d)
    (functorHomPrecomp (dgNerve.map H0 ≫ L) (dgNerve.map H1 ≫ L) (dgNerve.map J) d)
    h0 h1 (dgModuleRawOutputPrecompHom_heq R E K A J H0 H1 d) (dgNerve.map G)
  have hb := heq_of_eq (functorHomPrecomp_precomp (dgNerve.map H0 ≫ L)
    (dgNerve.map H1 ≫ L) (dgNerve.map J) (dgNerve.map G) d)
  have hc := functorHomPrecomp_heq_of_source_eq d (dgNerve.map_comp G J).symm
  exact ha.trans (hb.trans hc)
end SerrePositivity.InfinityCategories
