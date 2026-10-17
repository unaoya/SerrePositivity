module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionRepresentable
public import SerrePositivity.DifferentialGraded.Endomorphism.ConeTriangleComparison
public import SerrePositivity.DifferentialGraded.Perfect.UniversalProperty

/-! # graph tensor の有限 cell 像

dg 圏の分解は使わず、加群の射影置換と有限操作の木を使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- shift、有限和、標準 cone を保存する加群上の関手に対する有限操作の帰納法。 -/
lemma finiteCellCode_image_mem
    (H : ModuleCategory A D ⥤ DerivedModuleCategory A E) [H.Additive] [H.CommShift ℤ]
    (hcone : ∀ {M N : ModuleCategory A D} (f : M ⟶ N),
      H.mapTriangle.obj (moduleConeTriangle A D f) ∈ distTriang (DerivedModuleCategory A E))
    (P : ObjectProperty (DerivedModuleCategory A E)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] {S : Set D}
    (hgen : ∀ x ∈ S, P (H.obj (ForgetEnrichment.of (Complex A) (representable A x))))
    {M : ModuleCategory A D} (c : ModuleFiniteCellCode A D S M) : P (H.obj M) := by
  induction c with
  | zero => exact P.prop_of_isZero (H.map_isZero (moduleZero_isZero A D))
  | generator x hx => exact hgen x hx
  | @shift M s c ih =>
    exact P.prop_of_iso ((H.commShiftIso s).app M).symm (P.le_shift s _ ih)
  | @sum M N c d ihc ihd =>
    have : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
    have h := P.ext_of_isTriangulatedClosed₂'
      (binaryBiproductTriangle (H.obj M) (H.obj N))
      (binaryBiproductTriangle_distinguished _ _) ihc ihd
    rw [ObjectProperty.isoClosure_eq_self] at h
    exact P.prop_of_iso (H.mapIso (moduleBiprodIso A D M N) ≪≫ H.mapBiprod M N).symm h
  | cone c d f ihc ihd =>
    have h := P.ext_of_isTriangulatedClosed₃' _ (hcone f) ihc ihd
    rw [ObjectProperty.isoClosure_eq_self] at h
    exact h
  | iso c e ih => exact P.prop_of_iso (H.mapIso e) ih

variable (F : DGFunctor A D E)
local instance : (dgModuleExtension A D E F).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A D E (dgModuleExtension A D E F)

/-- graph tensor の閉零関手の標準 cone 像は主導来圏で distinguished。 -/
lemma graphExtension_cone_distinguished {M N : ModuleCategory A D} (f : M ⟶ N) :
    ((dgModuleExtension A D E F).onClosed ⋙ moduleToDerived A E).mapTriangle.obj
      (moduleConeTriangle A D f) ∈ distTriang (DerivedModuleCategory A E) := by
  exact isomorphic_distinguished _ (moduleDerivedConeTriangle_distinguished A E
    ((dgModuleExtension A D E F).onClosed.map f)) _
    ((Functor.mapTriangleCompIso _ _).app _ ≪≫
      (moduleToDerived A E).mapTriangle.mapIso
        (dgModuleFunctorConeTriangleIso A D E (dgModuleExtension A D E F) f).symm)

/-- 射影置換を用いる導来拡張は、指定代表対象で検証した三角部分圏へ有限 cell を送る。 -/
lemma graphDerivedExtension_finiteCell_mem
    (P : ObjectProperty (DerivedModuleCategory A E)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] (S : Set D)
    (hgen : ∀ x ∈ S, P ((moduleToDerived A E).obj
      (ForgetEnrichment.of (Complex A) (representable A (F.obj x)))))
    {M : ModuleCategory A D} (hM : moduleFiniteCellOver A D S M) :
    P ((dgDerivedExtension A D E F).obj ((moduleToDerived A D).obj M)) := by
  obtain ⟨c⟩ := hM
  have h := finiteCellCode_image_mem A D E
    ((dgModuleExtension A D E F).onClosed ⋙ moduleToDerived A E)
    (graphExtension_cone_distinguished A D E F) P
    (fun x hx => P.prop_of_iso
      ((moduleToDerived A E).mapIso (dgModuleExtensionRepresentableIso A D E F x)).symm
      (hgen x hx)) c
  exact P.prop_of_iso
    (dgDerivedExtensionResolutionComputation A D E F
      (moduleIdentityProjectiveResolution A D M
        (moduleFiniteCellOver_homotopicallyProjective A D ⟨c⟩))).symm h

/-- 導来有限 cell の本質像についても、同じ代表対象による判定が使える。 -/
lemma graphDerivedExtension_derivedFiniteCell_mem
    (P : ObjectProperty (DerivedModuleCategory A E)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] (S : Set D)
    (hgen : ∀ x ∈ S, P ((moduleToDerived A E).obj
      (ForgetEnrichment.of (Complex A) (representable A (F.obj x)))))
    {X : DerivedModuleCategory A D} (hX : derivedFiniteCellOver A D S X) :
    P ((dgDerivedExtension A D E F).obj X) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hX
  exact P.prop_of_iso ((dgDerivedExtension A D E F).mapIso e)
    (graphDerivedExtension_finiteCell_mem A D E F P S hgen hM)

end SerrePositivity.DifferentialGraded.DGQuotient
