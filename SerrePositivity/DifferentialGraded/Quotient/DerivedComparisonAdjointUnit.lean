module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionUnitComputation

/-! # 代表加群上の導来随伴と実際の比較写像の整合性

普通の加群の射影置換のみを使い、Hom 比較の正規化を固定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 標準の射影置換の増強を延長して得る、導来延長から underived 延長への比較。 -/
def derivedExtensionUnderivedMap (M : ModuleCategory A D) :
    (dgDerivedExtension A D E F).obj ((moduleToDerived A D).obj M) ⟶
      (moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj M) :=
  (dgDerivedExtensionResolutionComputation A D E F
      (moduleCanonicalProjectiveResolution A D M)).hom ≫
    (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map
      (moduleCanonicalProjectiveResolution A D M).π)

/-- 実際の加群射への転置は、導来比較と可換である。 -/
lemma derivedExtensionUnderivedMap_homEquiv (M : ModuleCategory A D)
    (N : ModuleCategory A E) (s : (dgModuleExtension A D E F).onClosed.obj M ⟶ N) :
    dgDerivedExtensionHomEquiv A D E F ((moduleToDerived A D).obj M)
      ((moduleToDerived A E).obj N)
      (derivedExtensionUnderivedMap A D E F M ≫ (moduleToDerived A E).map s) =
    (moduleToDerived A D).map
      ((dgModuleEnrichedRestrictionAdjunction A D E F).homEquiv M N s) ≫
        (dgDerivedRestrictionComputation A D E F N).inv := by
  change dgDerivedExtensionHomEquivOnModules A D E F M N _ = _
  rw [dgDerivedExtensionHomEquivOnModules_apply]
  unfold derivedExtensionUnderivedMap
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← CategoryTheory.Functor.map_comp, dgProjectiveDerivedExtensionHomEquiv_map,
    Adjunction.homEquiv_naturality_left, CategoryTheory.Functor.map_comp]
  simp only [← Category.assoc]
  have hi := (moduleDerivedIso A D (moduleCanonicalProjectiveResolution A D M).π
    (moduleCanonicalProjectiveResolution A D M).quasiIso).inv_hom_id
  change (moduleDerivedIso A D (moduleCanonicalProjectiveResolution A D M).π
    (moduleCanonicalProjectiveResolution A D M).quasiIso).inv ≫
      (moduleToDerived A D).map (moduleCanonicalProjectiveResolution A D M).π = 𝟙 _ at hi
  rw [hi, Category.id_comp]

/-- ホモトピー射影的な加群では、この比較は同型である。 -/
lemma derivedExtensionUnderivedMap_isIso (M : ModuleCategory A D)
    (hM : moduleHomotopicallyProjective A D M) :
    IsIso (derivedExtensionUnderivedMap A D E F M) := by
  have h := moduleToDerived_inverts A E _
    (dgModuleExtension_projective_quasiIso A D E F
      (moduleCanonicalProjectiveResolution A D M).projective hM
      (moduleCanonicalProjectiveResolution A D M).π
      (moduleCanonicalProjectiveResolution A D M).quasiIso)
  let := h
  unfold derivedExtensionUnderivedMap
  infer_instance

/-- 随伴の転置が元の Hom 包含となるように正規化した代表加群の延長同型。 -/
def derivedExtensionRepresentableUnitIso (z : D) :
    (dgDerivedExtension A D E F).obj
        ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A z))) ≅
      (moduleToDerived A E).obj
        (ForgetEnrichment.of (Complex A) (representable A (F.obj z))) := by
  let M := ForgetEnrichment.of (Complex A) (representable A z)
  let := derivedExtensionUnderivedMap_isIso A D E F M
    (representable_homotopicallyProjective A D z)
  exact asIso (derivedExtensionUnderivedMap A D E F M) ≪≫
    (moduleToDerived A E).mapIso (dgModuleExtensionRepresentableIso A D E F z)

/-- 上の代表同型を転置すると、既存の代表加群比較写像を得る。 -/
lemma derivedExtensionRepresentableUnitIso_homEquiv (z : D) :
    dgDerivedExtensionHomEquiv A D E F
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A z)))
      ((moduleToDerived A E).obj
        (ForgetEnrichment.of (Complex A) (representable A (F.obj z))))
      (derivedExtensionRepresentableUnitIso A D E F z).hom =
    (moduleToDerived A D).map (representableRestrictionMap A D E F z) ≫
      (dgDerivedRestrictionComputation A D E F
        (ForgetEnrichment.of (Complex A) (representable A (F.obj z)))).inv := by
  change dgDerivedExtensionHomEquiv A D E F _ _
    (derivedExtensionUnderivedMap A D E F _ ≫
      (moduleToDerived A E).map (dgModuleExtensionRepresentableIso A D E F z).hom) = _
  rw [derivedExtensionUnderivedMap_homEquiv, Adjunction.homEquiv_unit,
    dgModuleEnrichedRestrictionAdjunction_unit]
  rw [dgModuleRestriction_map]
  exact congrArg (fun t => (moduleToDerived A D).map t ≫
    (dgDerivedRestrictionComputation A D E F
      (ForgetEnrichment.of (Complex A) (representable A (F.obj z)))).inv)
    (functorExtensionUnit_representable A D E F z)


end SerrePositivity.DifferentialGraded.DGQuotient
