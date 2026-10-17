module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtension

/-! # 射影解像度によるgraph導来延長計算の自然性

## 概要
射影解像度によるgraph導来延長計算の自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

private lemma functorEqComputationNaturality {C : Type*} {T : Type*}
    [Category* C] [Category* T] {G H : C ⥤ T} (h : G = H) {M N : C} (f : M ⟶ N) :
    G.map f ≫ (eqToIso (congrArg (fun J => J.obj N) h)).hom =
      (eqToIso (congrArg (fun J => J.obj M) h)).hom ≫ H.map f := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]

lemma dgExtensionHomotopyComputation_naturality {M N : ModuleCategory A D} (f : M ⟶ N) :
    (dgExtensionHomotopyToDerived A D E F).map ((moduleToHomotopy A D).map f) ≫
        (dgExtensionHomotopyComputation A D E F N).hom =
      (dgExtensionHomotopyComputation A D E F M).hom ≫
        (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map f) := by
  have h₂ := congrArg (moduleHomotopyToDerivedClosed A E).map
    (functorEqComputationNaturality (dgModuleExtension A D E F).onHomotopy_fac f)
  simp only [Functor.map_comp, Functor.comp_map] at h₂
  have h₃ := (moduleToHomotopyDerivedIso A E).hom.naturality
    ((dgModuleExtension A D E F).onClosed.map f)
  change (moduleHomotopyToDerivedClosed A E).map
    ((toHomotopy A (RightModule A E)).map ((dgModuleExtension A D E F).onClosed.map f)) ≫
      ((moduleToHomotopyDerivedIso A E).app ((dgModuleExtension A D E F).onClosed.obj N)).hom =
    ((moduleToHomotopyDerivedIso A E).app ((dgModuleExtension A D E F).onClosed.obj M)).hom ≫
      (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map f) at h₃
  have h₄ := congrArg (fun t => t ≫
    ((moduleToHomotopyDerivedIso A E).app ((dgModuleExtension A D E F).onClosed.obj N)).hom) h₂
  have h₅ := congrArg (fun t => (moduleHomotopyToDerivedClosed A E).map
    (eqToIso (congrArg (fun G => G.obj M) (dgModuleExtension A D E F).onHomotopy_fac)).hom ≫ t) h₃
  simp only [Category.assoc] at h₄ h₅
  dsimp only [dgExtensionHomotopyComputation, dgExtensionHomotopyToDerived,
    Functor.comp_map, Functor.mapIso_hom, Iso.trans_hom]
  simp only [Category.assoc]
  exact h₄.trans h₅

lemma dgResolutionDerivedExtensionComputation_naturality
    (R : ∀ N : ModuleCategory A D, ModuleProjectiveResolution A D N)
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (dgResolutionDerivedExtension A D E F R).map ((moduleToDerived A D).map f) ≫
        (dgResolutionDerivedExtensionComputation A D E F R N).hom =
      (dgResolutionDerivedExtensionComputation A D E F R M).hom ≫
        (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map
          ((R M).lift (R N) f)) := by
  let H := dgExtensionHomotopyToDerived A D E F
  have h₁ := congrArg H.map ((moduleDerivedResolutionFunctor_fac A D R).hom.naturality f)
  simp only [Functor.map_comp] at h₁
  change H.map ((moduleDerivedResolutionFunctor A D R).map ((moduleToDerived A D).map f)) ≫
      H.map (moduleDerivedResolutionComputation A D R N).hom =
    H.map (moduleDerivedResolutionComputation A D R M).hom ≫
      H.map ((moduleToHomotopy A D).map ((R M).lift (R N) f)) at h₁
  change H.map _ ≫ (H.map _ ≫ _) = (H.map _ ≫ _) ≫ _
  rw [← Category.assoc, h₁]
  simp only [Category.assoc]
  exact congrArg (fun t => H.map (moduleDerivedResolutionComputation A D R M).hom ≫ t)
    (dgExtensionHomotopyComputation_naturality A D E F ((R M).lift (R N) f))

lemma dgDerivedExtensionResolutionComputation_canonical (M : ModuleCategory A D) :
    dgDerivedExtensionResolutionComputation A D E F (moduleCanonicalProjectiveResolution A D M) =
      dgResolutionDerivedExtensionComputation A D E F
        (moduleCanonicalProjectiveResolution A D) M := by
  apply Iso.ext
  change (dgExtensionHomotopyToDerived A D E F).map
      ((moduleDerivedResolutionComputation A D (moduleCanonicalProjectiveResolution A D) M).hom ≫
        (moduleToHomotopy A D).map ((moduleCanonicalProjectiveResolution A D M).comparison
          (moduleCanonicalProjectiveResolution A D M))) ≫
      (dgExtensionHomotopyComputation A D E F
        (moduleCanonicalProjectiveResolution A D M).obj).hom = _
  rw [ModuleProjectiveResolution.comparison_self, Category.comp_id]
  rfl

lemma dgDerivedExtensionResolutionComputation_inv_naturality {M N : ModuleCategory A D}
    (f : M ⟶ N) :
    (dgDerivedExtensionResolutionComputation A D E F
        (moduleCanonicalProjectiveResolution A D M)).inv ≫
        (dgDerivedExtension A D E F).map ((moduleToDerived A D).map f) =
      (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map
        ((moduleCanonicalProjectiveResolution A D M).lift
          (moduleCanonicalProjectiveResolution A D N) f)) ≫
        (dgDerivedExtensionResolutionComputation A D E F
          (moduleCanonicalProjectiveResolution A D N)).inv := by
  rw [dgDerivedExtensionResolutionComputation_canonical,
    dgDerivedExtensionResolutionComputation_canonical]
  dsimp only [dgDerivedExtension]
  have h := dgResolutionDerivedExtensionComputation_naturality A D E F
    (moduleCanonicalProjectiveResolution A D) f
  apply (cancel_mono (dgResolutionDerivedExtensionComputation A D E F
    (moduleCanonicalProjectiveResolution A D) N).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

end SerrePositivity.DifferentialGraded
