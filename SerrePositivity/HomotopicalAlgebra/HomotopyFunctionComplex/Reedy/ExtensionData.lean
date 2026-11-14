module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Adjoin
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Boundary

/-! # Boundary factorizations give the attaching data of a Reedy extension -/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J)
  {C : Type u'} [Category.{v'} C] (H : Lower r (r.deg j) ⥤ C)

/-- The three gluing laws needed to extend a lower-degree diagram at one object. -/
structure BoundaryExtension where
  obj : C
  incoming {x : Lower r (r.deg j)} (f : x.obj ⟶ j) (hf : direct f) : H.obj x ⟶ obj
  outgoing {x : Lower r (r.deg j)} (f : j ⟶ x.obj) (hf : inverse f) : obj ⟶ H.obj x
  incoming_naturality {x y : Lower r (r.deg j)} (f : x ⟶ y) (g : y.obj ⟶ j)
    (hg : direct g) (hfg : direct (f.hom ≫ g)) :
    H.map f ≫ incoming g hg = incoming (f.hom ≫ g) hfg
  outgoing_naturality {x y : Lower r (r.deg j)} (f : j ⟶ x.obj) (g : x ⟶ y)
    (hf : inverse f) (hfg : inverse (f ≫ g.hom)) :
    outgoing f hf ≫ H.map g = outgoing (f ≫ g.hom) hfg
  crossing {x y : Lower r (r.deg j)} (f : x.obj ⟶ j) (g : j ⟶ y.obj)
    (hf : direct f) (hg : inverse g) :
    incoming f hf ≫ outgoing g hg = H.map (ObjectProperty.homMk (f ≫ g))

variable [HasColimitsOfShape (LatchingIndex r j) C]
  [HasLimitsOfShape (MatchingIndex r j) C] {left right : MorphismProperty C}

abbrev boundaryExtension (q : MorphismProperty.MapFactorizationData left right
    (lowerBoundary r j H)) : BoundaryExtension r j H where
  obj := q.Z
  incoming {x} f hf := colimit.ι (latchingSourceLower r j ⋙ H)
    ⟨Over.mk f, hf, not_identities_into_top r j x f⟩ ≫ q.i
  outgoing {x} f hf := q.p ≫ limit.π (matchingTargetLower r j ⋙ H)
    ⟨Under.mk f, hf, not_identities_from_top r j x f⟩
  incoming_naturality {x y} f g hg hfg := by
    let a : LatchingIndex r j := ⟨Over.mk (f.hom ≫ g), hfg,
      not_identities_into_top r j x _⟩
    let b : LatchingIndex r j := ⟨Over.mk g, hg, not_identities_into_top r j y _⟩
    let φ : a ⟶ b := ObjectProperty.homMk (Over.homMk f.hom)
    have h := colimit.w (latchingSourceLower r j ⋙ H) φ
    change H.map f ≫ colimit.ι (latchingSourceLower r j ⋙ H) b =
      colimit.ι (latchingSourceLower r j ⋙ H) a at h
    simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ q.i) h
  outgoing_naturality {x y} f g hf hfg := by
    let a : MatchingIndex r j := ⟨Under.mk f, hf, not_identities_from_top r j x _⟩
    let b : MatchingIndex r j := ⟨Under.mk (f ≫ g.hom), hfg,
      not_identities_from_top r j y _⟩
    let φ : a ⟶ b := ObjectProperty.homMk (Under.homMk g.hom)
    have h := limit.w (matchingTargetLower r j ⋙ H) φ
    change limit.π (matchingTargetLower r j ⋙ H) a ≫ H.map g =
      limit.π (matchingTargetLower r j ⋙ H) b at h
    simpa only [Category.assoc] using congrArg (fun k ↦ q.p ≫ k) h
  crossing {x y} f g hf hg := by
    let a : LatchingIndex r j := ⟨Over.mk f, hf, not_identities_into_top r j x _⟩
    let b : MatchingIndex r j := ⟨Under.mk g, hg, not_identities_from_top r j y _⟩
    change (colimit.ι (latchingSourceLower r j ⋙ H) a ≫ q.i) ≫
      (q.p ≫ limit.π (matchingTargetLower r j ⋙ H) b) = _
    rw [Category.assoc, ← Category.assoc q.i, q.fac]
    exact ι_lowerBoundary_π r j H a b

end SerrePositivity.Reedy

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.2.9.15" (partial := direction) "仮定：指定次数の低次部分圏に一つの対象を追加し、L→M の分解を与える（Lean が強い特殊形）。結論：同じ境界分解の中間対象を新しい頂点とする延長 functor を構成し、その元の下方図式への制限同型を得る。原典の (2) から (1) の方向に一致するが、任意 good filtration における二つのデータの同値は含まない。"] _root_.SerrePositivity.Reedy.boundaryExtension
