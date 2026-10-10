module

public import SerrePositivity.HomologicalAlgebra.TorLES

/-! # 零次 Tor とテンソル積の比較の両変数での自然性

Tor の長完全列の標準の射を、零次では実際のテンソル積の射と同定する。
両変数の導来計算を比較する際に、一次 Tor を同じ核として表すために使う。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory Limits MonoidalCategory HomologicalComplex

set_option backward.isDefEq.respectTransparency false

/-- 零次左導来関手から元の関手への射は、関手の間の自然変換と可換である。 -/
@[reassoc]
lemma fromLeftDerivedZero_natTrans
    {C D : Type*} [Category* C] [Abelian C] [HasProjectiveResolutions C] [Category* D] [Abelian D]
    (F G : C ⥤ D) [F.Additive] [G.Additive] (α : F ⟶ G) (X : C) :
    (NatTrans.leftDerived α 0).app X ≫ G.fromLeftDerivedZero.app X =
      F.fromLeftDerivedZero.app X ≫ α.app X := by
  let P := projectiveResolution X
  rw [P.leftDerived_app_eq α 0, P.fromLeftDerivedZero_eq G, P.fromLeftDerivedZero_eq F]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  change homologyMap ((NatTrans.mapHomologicalComplex α _).app P.complex) 0 ≫
      homologyι _ 0 ≫ P.fromLeftDerivedZero' G =
    homologyι _ 0 ≫ P.fromLeftDerivedZero' F ≫ α.app X
  rw [homologyι_naturality_assoc]
  congr 1
  apply (cancel_epi (pOpcycles ((F.mapHomologicalComplex _).obj P.complex) 0)).mp
  simp only [p_opcyclesMap_assoc, ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero',
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc,
    NatTrans.mapHomologicalComplex_app_f]
  exact (α.naturality (P.π.f 0)).symm

variable {R : Type u} [CommRing R]

/-- 零次 Tor とテンソル積の同型は第1変数の射と可換である。 -/
@[reassoc]
lemma torZeroIso_naturality_left {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    ((Tor (ModuleCat R) 0).map f).app N ≫ (torModuleZeroEquiv R M' N).toModuleIso.hom =
      (torModuleZeroEquiv R M N).toModuleIso.hom ≫ ((tensoringLeft (ModuleCat R)).map f).app N := by
  exact fromLeftDerivedZero_natTrans _ _ ((tensoringLeft _).map f) N

/-- 零次 Tor とテンソル積の同型は第2変数の射と可換である。 -/
@[reassoc]
lemma torZeroIso_naturality_right (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R} (f : N ⟶ N') :
    ((Tor (ModuleCat R) 0).obj M).map f ≫ (torModuleZeroEquiv R M N').toModuleIso.hom =
      (torModuleZeroEquiv R M N).toModuleIso.hom ≫ (tensorLeft M).map f :=
  (tensorLeft M).leftDerivedZeroIsoSelf.hom.naturality f

/-- 零次 Tor の変数交換。テンソル積の対称性から得る。 -/
noncomputable def torZeroComm (M N : ModuleCat.{u} R) :
    ModuleCat.of R (TorModule R 0 M N) ≅ ModuleCat.of R (TorModule R 0 N M) :=
  (torModuleZeroEquiv R M N).toModuleIso ≪≫ (β_ M N) ≪≫
    (torModuleZeroEquiv R N M).toModuleIso.symm

/-- 零次の変数交換は、第1変数の射を交換後の第2変数の射に送る。 -/
@[reassoc]
lemma torZeroComm_naturality_left {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    ((Tor (ModuleCat R) 0).map f).app N ≫ (torZeroComm M' N).hom =
      (torZeroComm M N).hom ≫ ((Tor (ModuleCat R) 0).obj N).map f := by
  apply (cancel_mono (torModuleZeroEquiv R N M').toModuleIso.hom).mp
  simp only [torZeroComm, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, torZeroIso_naturality_right, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, torZeroIso_naturality_left, Category.assoc]
  exact congrArg (fun t ↦ (torModuleZeroEquiv R M N).toModuleIso.hom ≫ t)
    (BraidedCategory.braiding_naturality_left f N)

end SerrePositivity
