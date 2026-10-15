module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Index

/-! # Constructing a functor from inverse and direct Reedy maps

Only composition inside each Reedy class and the interchange of a direct
map with an inverse map need to be checked. Uniqueness of the actual Reedy
factorization supplies the full functor and all its composition laws.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (C : Type u') [Category.{v'} C]

structure FunctorData (_r : ReedyStructure inverse direct α) (C : Type u') [Category.{v'} C] where
  obj : J → C
  mapInverse {i j : J} (f : i ⟶ j) (hf : inverse f) : obj i ⟶ obj j
  mapDirect {i j : J} (f : i ⟶ j) (hf : direct f) : obj i ⟶ obj j
  idInverse (j : J) : mapInverse (𝟙 j) (inverse.id_mem j) = 𝟙 (obj j)
  idDirect (j : J) : mapDirect (𝟙 j) (direct.id_mem j) = 𝟙 (obj j)
  compInverse {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (hf : inverse f) (hg : inverse g) :
    mapInverse (f ≫ g) (inverse.comp_mem f g hf hg) = mapInverse f hf ≫ mapInverse g hg
  compDirect {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (hf : direct f) (hg : direct g) :
    mapDirect (f ≫ g) (direct.comp_mem f g hf hg) = mapDirect f hf ≫ mapDirect g hg
  exchange {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (hf : direct f) (hg : inverse g)
    (q : MorphismProperty.MapFactorizationData inverse direct (f ≫ g)) :
    mapDirect f hf ≫ mapInverse g hg = mapInverse q.i q.hi ≫ mapDirect q.p q.hp

namespace FunctorData
variable {r C} (d : FunctorData r C)

abbrev map {i j : J} (f : i ⟶ j) : d.obj i ⟶ d.obj j :=
  d.mapInverse (r.mapFactorizationData f).i (r.mapFactorizationData f).hi ≫
    d.mapDirect (r.mapFactorizationData f).p (r.mapFactorizationData f).hp

lemma map_eq {i j : J} (f : i ⟶ j)
    (q : MorphismProperty.MapFactorizationData inverse direct f) :
    d.map f = d.mapInverse q.i q.hi ≫ d.mapDirect q.p q.hp := by
  have : Subsingleton (MorphismProperty.MapFactorizationData inverse direct f) :=
    r.subsingleton_mapFactorizationData f
  have h : r.mapFactorizationData f = q := Subsingleton.elim _ _
  exact congrArg (fun q : MorphismProperty.MapFactorizationData inverse direct f ↦
    d.mapInverse q.i q.hi ≫ d.mapDirect q.p q.hp) h

lemma map_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) :
    d.map (f ≫ g) = d.map f ≫ d.map g := by
  let df := r.mapFactorizationData f
  let dg := r.mapFactorizationData g
  let dm := r.mapFactorizationData (df.p ≫ dg.i)
  let q : MorphismProperty.MapFactorizationData inverse direct (f ≫ g) :=
    { Z := dm.Z
      i := df.i ≫ dm.i
      p := dm.p ≫ dg.p
      hi := inverse.comp_mem _ _ df.hi dm.hi
      hp := direct.comp_mem _ _ dm.hp dg.hp
      fac := by simp only [Category.assoc, reassoc_of% dm.fac, reassoc_of% df.fac, dg.fac] }
  rw [d.map_eq _ q]
  change d.mapInverse (df.i ≫ dm.i) _ ≫ d.mapDirect (dm.p ≫ dg.p) _ = _
  rw [d.compInverse df.i dm.i df.hi dm.hi, d.compDirect dm.p dg.p dm.hp dg.hp]
  calc
    _ = d.mapInverse df.i df.hi ≫ (d.mapInverse dm.i dm.hi ≫ d.mapDirect dm.p dm.hp) ≫
        d.mapDirect dg.p dg.hp := by simp only [Category.assoc]
    _ = d.mapInverse df.i df.hi ≫ (d.mapDirect df.p df.hp ≫ d.mapInverse dg.i dg.hi) ≫
        d.mapDirect dg.p dg.hp := by rw [← d.exchange df.p dg.i df.hp dg.hi dm]
    _ = d.map f ≫ d.map g := by simp only [map, df, dg, Category.assoc]

lemma map_id (j : J) : d.map (𝟙 j) = 𝟙 (d.obj j) := by
  rw [d.map_eq _ (.mk j (𝟙 j) (𝟙 j) (Category.comp_id _) (inverse.id_mem j) (direct.id_mem j)),
    d.idInverse, d.idDirect, Category.id_comp]

def toFunctor : J ⥤ C where
  obj := d.obj
  map := d.map
  map_id := d.map_id
  map_comp := d.map_comp

lemma toFunctor_map_inverse {i j : J} (f : i ⟶ j) (hf : inverse f) :
    d.toFunctor.map f = d.mapInverse f hf := by
  change d.map f = _
  rw [d.map_eq _ (.mk j f (𝟙 j) (Category.comp_id _) hf (direct.id_mem j)),
    d.idDirect, Category.comp_id]

lemma toFunctor_map_direct {i j : J} (f : i ⟶ j) (hf : direct f) :
    d.toFunctor.map f = d.mapDirect f hf := by
  change d.map f = _
  rw [d.map_eq _ (.mk i (𝟙 i) f (Category.id_comp _) (inverse.id_mem i) hf),
    d.idInverse, Category.id_comp]

def ofFunctor (r : ReedyStructure inverse direct α) (F : J ⥤ C) : FunctorData r C where
  obj := F.obj
  mapInverse f _ := F.map f
  mapDirect f _ := F.map f
  idInverse := F.map_id
  idDirect := F.map_id
  compInverse f g _ _ := F.map_comp f g
  compDirect f g _ _ := F.map_comp f g
  exchange f g _ _ q :=
    (F.map_comp f g).symm.trans
      ((congrArg (fun h ↦ F.map h) q.fac.symm).trans (F.map_comp q.i q.p))

lemma ofFunctor_toFunctor_map (r : ReedyStructure inverse direct α) (F : J ⥤ C)
    {i j : J} (f : i ⟶ j) : (ofFunctor r F).toFunctor.map f = F.map f := by
  change F.map (r.mapFactorizationData f).i ≫ F.map (r.mapFactorizationData f).p = F.map f
  rw [← F.map_comp, (r.mapFactorizationData f).fac]

end FunctorData
end SerrePositivity.Reedy
