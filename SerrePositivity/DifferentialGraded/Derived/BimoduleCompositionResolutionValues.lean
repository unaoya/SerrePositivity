module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionResolution

/-! # 指定解像度による導来合成の値の計算と増大squareの整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]

omit [Small.{u} E] in
lemma derivedComposeWithMap_computation {R S : RightKFlatBimoduleCategory A C E}
    (r : R ⟶ S) (P : BimoduleCategory A B C) :
    (derivedComposeWithMap A B C E R.property S.property r.hom).app
        ((bimoduleToDerived A B C).obj P) ≫
      (derivedComposeWithComputation A B C E S.obj S.property P).hom =
    (derivedComposeWithComputation A B C E R.obj R.property P).hom ≫
      (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) r.hom) := by
  rw [derivedComposeWithMap_app]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 全導来合成の指定解像度による値での計算同型。 -/
def derivedBimoduleComposeResolutionValueIso (hE : localHomKFlat A E)
    (Q : BimoduleCategory A C E) (R : RightKFlatBimoduleCategory A C E)
    (q : R.obj ⟶ Q) (hq : BimoduleCategory.quasiIso A C E q) (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q)).obj
        ((bimoduleToDerived A B C).obj P) ≅
      (bimoduleToDerived A B E).obj ((composeWith A B C E R.obj).obj P) :=
  (derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).app
    ((bimoduleToDerived A B C).obj P) ≪≫
      derivedComposeWithComputation A B C E R.obj R.property P

/-- 増大squareの導来可換性から、値の計算同型の変換則を得る。 -/
lemma derivedBimoduleComposeResolutionValueIso_change (hE : localHomKFlat A E)
    (Q : BimoduleCategory A C E) (R S : RightKFlatBimoduleCategory A C E)
    (q : R.obj ⟶ Q) (s : S.obj ⟶ Q)
    (hq : BimoduleCategory.quasiIso A C E q) (hs : BimoduleCategory.quasiIso A C E s)
    (r : R ⟶ S)
    (h : (bimoduleToDerived A C E).map q =
      (bimoduleToDerived A C E).map r.hom ≫ (bimoduleToDerived A C E).map s)
    (P : BimoduleCategory A B C) :
    (derivedBimoduleComposeResolutionValueIso A B C E hE Q S s hs P).hom =
      (derivedBimoduleComposeResolutionValueIso A B C E hE Q R q hq P).hom ≫
        (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) r.hom) := by
  have hn := derivedBimoduleComposeResolutionComputation_naturality A B C E hE
    R S q s hq hs (𝟙 Q) r (by
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact h)
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  have hv := NatTrans.congr_app hn ((bimoduleToDerived A B C).obj P)
  change (derivedBimoduleComposeResolutionComputation A B C E hE Q S s hs).hom.app
      ((bimoduleToDerived A B C).obj P) =
    (derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).hom.app
      ((bimoduleToDerived A B C).obj P) ≫
        (derivedComposeWithMap A B C E R.property S.property r.hom).app
          ((bimoduleToDerived A B C).obj P) at hv
  dsimp only [derivedBimoduleComposeResolutionValueIso, Iso.trans_hom]
  simp only [Iso.app_hom]
  rw [hv, Category.assoc, derivedComposeWithMap_computation, ← Category.assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
