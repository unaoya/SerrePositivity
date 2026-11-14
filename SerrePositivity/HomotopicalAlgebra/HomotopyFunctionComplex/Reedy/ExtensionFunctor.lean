module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionData
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorData

/-! # The actual functor obtained by a one-object Reedy extension

The boundary gluing laws imply all composition laws, including composites
through the new object. Unique Reedy factorization then supplies the maps
on arbitrary morphisms of the extended indexing category.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy.BoundaryExtension
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  {r : ReedyStructure inverse direct α} {j : J}
  {C : Type u'} [Category.{v'} C] {H : Lower r (r.deg j) ⥤ C}
  (d : BoundaryExtension r j H)

abbrev object : Adjoin r j → C
  | none => d.obj
  | some x => H.obj x

def inverseMap {x y : Adjoin r j} (f : x ⟶ y)
    (hf : inducedInverse (inverse := inverse) (adjoinObj r j) f) :
    d.object x ⟶ d.object y := by
  cases x with
  | none =>
    cases y with
    | none => exact 𝟙 d.obj
    | some y => exact d.outgoing f.hom hf
  | some x =>
    cases y with
    | none => exact (not_inverse_into_top r j x f.hom hf).elim
    | some y => exact H.map (ObjectProperty.homMk f.hom)

def directMap {x y : Adjoin r j} (f : x ⟶ y)
    (hf : inducedDirect (direct := direct) (adjoinObj r j) f) :
    d.object x ⟶ d.object y := by
  cases x with
  | none =>
    cases y with
    | none => exact 𝟙 d.obj
    | some y => exact (not_direct_from_top r j y f.hom hf).elim
  | some x =>
    cases y with
    | none => exact d.incoming f.hom hf
    | some y => exact H.map (ObjectProperty.homMk f.hom)

lemma inverseMap_id (x : Adjoin r j) :
    d.inverseMap (𝟙 x) ((inducedInverse (inverse := inverse) (adjoinObj r j)).id_mem x) =
      𝟙 (d.object x) := by
  cases x with
  | none => rfl
  | some x => exact H.map_id x

lemma directMap_id (x : Adjoin r j) :
    d.directMap (𝟙 x) ((inducedDirect (direct := direct) (adjoinObj r j)).id_mem x) =
      𝟙 (d.object x) := by
  cases x with
  | none => rfl
  | some x => exact H.map_id x

lemma inverseMap_comp {x y z : Adjoin r j} (f : x ⟶ y) (g : y ⟶ z)
    (hf : inducedInverse (inverse := inverse) (adjoinObj r j) f)
    (hg : inducedInverse (inverse := inverse) (adjoinObj r j) g) :
    d.inverseMap (f ≫ g) ((inducedInverse (inverse := inverse) _).comp_mem _ _ hf hg) =
      d.inverseMap f hf ≫ d.inverseMap g hg := by
  cases x with
  | none =>
    cases y with
    | none =>
      have h : f = @CategoryStruct.id (Adjoin r j) _ none :=
        InducedCategory.hom_ext (inverse_top_endomorphism r j f.hom hf)
      subst f
      cases z <;> simp only [Category.id_comp, inverseMap, Category.id_comp]
    | some y =>
      cases z with
      | none => exact (not_inverse_into_top r j y g.hom hg).elim
      | some z =>
        exact (d.outgoing_naturality f.hom (ObjectProperty.homMk g.hom) hf
          (inverse.comp_mem _ _ hf hg)).symm
  | some x =>
    cases y with
    | none => exact (not_inverse_into_top r j x f.hom hf).elim
    | some y =>
      cases z with
      | none => exact (not_inverse_into_top r j y g.hom hg).elim
      | some z => exact H.map_comp (ObjectProperty.homMk f.hom) (ObjectProperty.homMk g.hom)

lemma directMap_comp {x y z : Adjoin r j} (f : x ⟶ y) (g : y ⟶ z)
    (hf : inducedDirect (direct := direct) (adjoinObj r j) f)
    (hg : inducedDirect (direct := direct) (adjoinObj r j) g) :
    d.directMap (f ≫ g) ((inducedDirect (direct := direct) _).comp_mem _ _ hf hg) =
      d.directMap f hf ≫ d.directMap g hg := by
  cases z with
  | none =>
    cases y with
    | none =>
      have h : g = @CategoryStruct.id (Adjoin r j) _ none :=
        InducedCategory.hom_ext (direct_top_endomorphism r j g.hom hg)
      subst g
      cases x <;> simp only [Category.comp_id, directMap, Category.comp_id]
    | some y =>
      cases x with
      | none => exact (not_direct_from_top r j y f.hom hf).elim
      | some x =>
        exact (d.incoming_naturality (ObjectProperty.homMk f.hom) g.hom hg
          (direct.comp_mem _ _ hf hg)).symm
  | some z =>
    cases y with
    | none => exact (not_direct_from_top r j z g.hom hg).elim
    | some y =>
      cases x with
      | none => exact (not_direct_from_top r j y f.hom hf).elim
      | some x => exact H.map_comp (ObjectProperty.homMk f.hom) (ObjectProperty.homMk g.hom)

lemma exchange {x y z : Adjoin r j} (f : x ⟶ y) (g : y ⟶ z)
    (hf : inducedDirect (direct := direct) (adjoinObj r j) f)
    (hg : inducedInverse (inverse := inverse) (adjoinObj r j) g)
    (q : MorphismProperty.MapFactorizationData
      (inducedInverse (inverse := inverse) (adjoinObj r j))
      (inducedDirect (direct := direct) (adjoinObj r j)) (f ≫ g)) :
    d.directMap f hf ≫ d.inverseMap g hg = d.inverseMap q.i q.hi ≫ d.directMap q.p q.hp := by
  have := (adjoinReedy r j).subsingleton_mapFactorizationData (f ≫ g)
  cases y with
  | some y =>
    cases x with
    | none => exact (not_direct_from_top r j y f.hom hf).elim
    | some x =>
      cases z with
      | none => exact (not_inverse_into_top r j y g.hom hg).elim
      | some z =>
        rcases q with ⟨(_ | w), i, p, fac, hi, hp⟩
        · exact (not_inverse_into_top r j x i.hom hi).elim
        · change H.map (ObjectProperty.homMk f.hom) ≫
            H.map (ObjectProperty.homMk g.hom) =
            H.map (ObjectProperty.homMk i.hom) ≫ H.map (ObjectProperty.homMk p.hom)
          rw [← H.map_comp, ← H.map_comp]
          exact congrArg (fun k ↦ H.map (ObjectProperty.homMk k))
            (congrArg (fun k ↦ k.hom) fac).symm
  | none =>
    cases x with
    | none =>
      have h : f = @CategoryStruct.id (Adjoin r j) _ none :=
        InducedCategory.hom_ext (direct_top_endomorphism r j f.hom hf)
      subst f
      have hq : q = MorphismProperty.MapFactorizationData.mk z g (𝟙 z)
          (by simp only [Category.comp_id, Category.id_comp]) hg
          ((inducedDirect (direct := direct) _).id_mem z) :=
        Subsingleton.elim _ _
      subst q
      change d.directMap (𝟙 _) _ ≫ d.inverseMap g hg =
        d.inverseMap g hg ≫ d.directMap (𝟙 _) _
      rw [d.directMap_id, d.directMap_id, Category.id_comp, Category.comp_id]
    | some x =>
      cases z with
      | none =>
        have h : g = @CategoryStruct.id (Adjoin r j) _ none :=
          InducedCategory.hom_ext (inverse_top_endomorphism r j g.hom hg)
        subst g
        have hq : q = MorphismProperty.MapFactorizationData.mk (C := Adjoin r j)
            (some x) (@CategoryStruct.id (Adjoin r j) _ (some x)) f
            (by simp only [Category.comp_id, Category.id_comp])
            ((inducedInverse (inverse := inverse) _).id_mem _) hf :=
          Subsingleton.elim _ _
        subst q
        change d.directMap f hf ≫ d.inverseMap (𝟙 _) _ =
          d.inverseMap (𝟙 _) _ ≫ d.directMap f hf
        rw [d.inverseMap_id, d.inverseMap_id, Category.id_comp, Category.comp_id]
      | some z =>
        rcases q with ⟨(_ | w), i, p, fac, hi, hp⟩
        · exact (not_inverse_into_top r j x i.hom hi).elim
        · change d.incoming f.hom hf ≫ d.outgoing g.hom hg =
            H.map (ObjectProperty.homMk i.hom) ≫ H.map (ObjectProperty.homMk p.hom)
          have hc := d.crossing f.hom g.hom hf hg
          rw [hc, ← H.map_comp]
          exact congrArg (fun k ↦ H.map (ObjectProperty.homMk k))
            (congrArg (fun k ↦ k.hom) fac).symm

def functorData : FunctorData (adjoinReedy r j) C where
  obj := d.object
  mapInverse := d.inverseMap
  mapDirect := d.directMap
  idInverse := d.inverseMap_id
  idDirect := d.directMap_id
  compInverse := d.inverseMap_comp
  compDirect := d.directMap_comp
  exchange := d.exchange

def toFunctor : Adjoin r j ⥤ C := d.functorData.toFunctor

lemma toFunctor_map_inverse {x y : Adjoin r j} (f : x ⟶ y)
    (hf : inverse f.hom) : d.toFunctor.map f = d.inverseMap f hf :=
  d.functorData.toFunctor_map_inverse f hf

lemma toFunctor_map_direct {x y : Adjoin r j} (f : x ⟶ y)
    (hf : direct f.hom) : d.toFunctor.map f = d.directMap f hf :=
  d.functorData.toFunctor_map_direct f hf


lemma toFunctor_map_lower {x y : Lower r (r.deg j)} (f : x ⟶ y) :
    d.toFunctor.map ((adjoinLower r j).map f) = H.map f := by
  let q := (adjoinReedy r j).mapFactorizationData ((adjoinLower r j).map f)
  change d.functorData.map ((adjoinLower r j).map f) = _
  rw [d.functorData.map_eq _ q]
  rcases q with ⟨(_ | w), i, p, fac, hi, hp⟩
  · exact (not_inverse_into_top r j x i.hom hi).elim
  · change H.map (ObjectProperty.homMk i.hom) ≫ H.map (ObjectProperty.homMk p.hom) = _
    rw [← H.map_comp]
    apply congrArg H.map
    apply ObjectProperty.hom_ext
    exact congrArg (fun k ↦ k.hom) fac

def restrictionIso : adjoinLower r j ⋙ d.toFunctor ≅ H :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    change d.toFunctor.map ((adjoinLower r j).map f) ≫ 𝟙 _ = 𝟙 _ ≫ H.map f
    rw [Category.comp_id, Category.id_comp, d.toFunctor_map_lower])

lemma toFunctor_map_incoming {x : Lower r (r.deg j)} (f : x.obj ⟶ j) (hf : direct f) :
    d.toFunctor.map (InducedCategory.homMk (X := some x) (Y := none) f) =
      d.incoming f hf := d.toFunctor_map_direct _ hf

lemma toFunctor_map_outgoing {x : Lower r (r.deg j)} (f : j ⟶ x.obj) (hf : inverse f) :
    d.toFunctor.map (InducedCategory.homMk (X := none) (Y := some x) f) =
      d.outgoing f hf := d.toFunctor_map_inverse _ hf

end SerrePositivity.Reedy.BoundaryExtension

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.2.9.15" (partial := direction) "仮定：指定次数の低次部分圏に一つの対象を追加し、L→M の分解を与える（Lean が強い特殊形）。結論：同じ境界分解の中間対象を新しい頂点とする延長 functor を構成し、その元の下方図式への制限同型を得る。原典の (2) から (1) の方向に一致するが、任意 good filtration における二つのデータの同値は含まない。"] _root_.SerrePositivity.Reedy.BoundaryExtension.restrictionIso
attribute [cite HTT "A.2.9.15" (partial := direction) "仮定：指定次数の低次部分圏に一つの対象を追加し、L→M の分解を与える（Lean が強い特殊形）。結論：同じ境界分解の中間対象を新しい頂点とする延長 functor を構成し、その元の下方図式への制限同型を得る。原典の (2) から (1) の方向に一致するが、任意 good filtration における二つのデータの同値は含まない。"] _root_.SerrePositivity.Reedy.BoundaryExtension.toFunctor
