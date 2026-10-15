module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionOfFunctor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionDegree

/-! # Comparing reconstructed extensions with the original diagrams -/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy.BoundaryExtension
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J)
  {C : Type u'} [Category.{v'} C] (F : J ⥤ C)

abbrev ofFunctorObjIso (x : Adjoin r j) :
    (ofFunctor r j F).object x ≅ F.obj (adjoinObj r j x) := by
  cases x <;> exact Iso.refl _

lemma ofFunctor_inverseMap {x y : Adjoin r j} (f : x ⟶ y) (hf : inverse f.hom) :
    (ofFunctor r j F).inverseMap f hf ≫ (ofFunctorObjIso r j F y).hom =
      (ofFunctorObjIso r j F x).hom ≫ F.map f.hom := by
  cases x with
  | none =>
    cases y with
    | none =>
      change 𝟙 (F.obj j) ≫ 𝟙 _ = 𝟙 _ ≫ F.map f.hom
      rw [inverse_top_endomorphism r j f.hom hf, F.map_id]
    | some y => exact (Category.comp_id _).trans (Category.id_comp _).symm
  | some x =>
    cases y with
    | none => exact (not_inverse_into_top r j x f.hom hf).elim
    | some y => exact (Category.comp_id _).trans (Category.id_comp _).symm

lemma ofFunctor_directMap {x y : Adjoin r j} (f : x ⟶ y) (hf : direct f.hom) :
    (ofFunctor r j F).directMap f hf ≫ (ofFunctorObjIso r j F y).hom =
      (ofFunctorObjIso r j F x).hom ≫ F.map f.hom := by
  cases x with
  | none =>
    cases y with
    | none =>
      change 𝟙 (F.obj j) ≫ 𝟙 _ = 𝟙 _ ≫ F.map f.hom
      rw [direct_top_endomorphism r j f.hom hf, F.map_id]
    | some y => exact (not_direct_from_top r j y f.hom hf).elim
  | some x =>
    cases y with
    | none => exact (Category.comp_id _).trans (Category.id_comp _).symm
    | some y => exact (Category.comp_id _).trans (Category.id_comp _).symm

lemma ofFunctor_toFunctor_map {x y : Adjoin r j} (f : x ⟶ y) :
    (ofFunctor r j F).toFunctor.map f ≫ (ofFunctorObjIso r j F y).hom =
      (ofFunctorObjIso r j F x).hom ≫ F.map f.hom := by
  let q := (adjoinReedy r j).mapFactorizationData f
  change ((ofFunctor r j F).inverseMap q.i q.hi ≫
      (ofFunctor r j F).directMap q.p q.hp) ≫ _ = _
  have hd := ofFunctor_directMap r j F q.p q.hp
  have hi := ofFunctor_inverseMap r j F q.i q.hi
  rw [Category.assoc, hd, ← Category.assoc, hi, Category.assoc, ← F.map_comp]
  exact congrArg (fun k ↦ (ofFunctorObjIso r j F x).hom ≫ F.map k)
    (congrArg (fun k ↦ k.hom) q.fac)

def ofFunctorIso : (ofFunctor r j F).toFunctor ≅ adjoinInclusion r j ⋙ F :=
  NatIso.ofComponents (ofFunctorObjIso r j F) (fun f ↦ ofFunctor_toFunctor_map r j F f)

lemma ofFunctorIso_naturality {G : J ⥤ C} (τ : F ⟶ G) :
    (mapOfNatTrans r j τ).toNatTrans ≫ (ofFunctorIso r j G).hom =
      (ofFunctorIso r j F).hom ≫ Functor.whiskerLeft (adjoinInclusion r j) τ := by
  ext x
  cases x <;> change τ.app _ ≫ 𝟙 _ = 𝟙 _ ≫ τ.app _ <;>
    rw [Category.id_comp, Category.comp_id]


abbrev indexInclusionIso (hinj : Function.Injective r.deg) :
    degreeIndex r j hinj ⋙ adjoinInclusion r j ≅ upperInclusion r (r.deg j) :=
  NatIso.ofComponents (fun x ↦ eqToIso (degreeIndexObj_eq r j hinj x)) (fun {x y} f ↦ by
    change (eqToHom (degreeIndexObj_eq r j hinj x) ≫ f.hom ≫
      eqToHom (degreeIndexObj_eq r j hinj y).symm) ≫
      eqToHom (degreeIndexObj_eq r j hinj y) =
      eqToHom (degreeIndexObj_eq r j hinj x) ≫ f.hom
    exact conjugate_eqToHom _ _ _)

def degreeOfFunctorIso (hinj : Function.Injective r.deg) :
    (ofFunctor r j F).degreeExtension hinj ≅ upperInclusion r (r.deg j) ⋙ F :=
  Functor.isoWhiskerLeft (degreeIndex r j hinj) (ofFunctorIso r j F) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (indexInclusionIso r j hinj) F

lemma degreeOfFunctorIso_naturality (hinj : Function.Injective r.deg)
    {G : J ⥤ C} (τ : F ⟶ G) :
    Functor.whiskerLeft (degreeIndex r j hinj) (mapOfNatTrans r j τ).toNatTrans ≫
      (degreeOfFunctorIso r j G hinj).hom =
    (degreeOfFunctorIso r j F hinj).hom ≫
      Functor.whiskerLeft (upperInclusion r (r.deg j)) τ := by
  ext x
  simp only [degreeOfFunctorIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    indexInclusionIso, ofFunctorIso, NatIso.ofComponents_hom_app, eqToIso,
    Category.id_comp]
  let z := (degreeIndex r j hinj).obj x
  have hz : adjoinObj r j z = x.obj := degreeIndexObj_eq r j hinj x
  have hm := congr_app (ofFunctorIso_naturality r j F τ) z
  change (mapOfNatTrans r j τ).app z ≫ (ofFunctorObjIso r j G z).hom =
    (ofFunctorObjIso r j F z).hom ≫ τ.app (adjoinObj r j z) at hm
  change (mapOfNatTrans r j τ).app z ≫
      ((ofFunctorObjIso r j G z).hom ≫ G.map (eqToHom hz)) =
    ((ofFunctorObjIso r j F z).hom ≫ F.map (eqToHom hz)) ≫
      τ.app x.obj
  have ht := τ.naturality (eqToHom hz)
  rw [← Category.assoc, hm, Category.assoc, ← ht]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.Reedy.BoundaryExtension
