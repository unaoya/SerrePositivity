module

public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionUnitComputation

/-!
概要：KST §3.1 の局所射影的加群上での指定係数拡大比較と随伴像。
方針：標準半自由分解の増大と通常 graph 延長の射を合成し、指定導来随伴で計算する。
規約：射影的始域に限って比較の可逆性を移す。存在する任意同型に置き換えない。
使われ方：局所 regular 生成元の canonical な係数拡大比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R]
variable (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (F : DGFunctor R C D)

/-- 概要：通常 graph 延長の射から標準分解を介した導来延長比較を構成する。
方針：標準分解の計算同型、増大の graph 延長、指定通常射を合成する。
規約：KST §3.1。使われ方：射影的加群での随伴比較の具体的な経路。 -/
def canonicalResolutionExtensionComparison (N : ModuleCategory R C) (M : ModuleCategory R D)
    (s : (dgModuleExtension R C D F).onClosed.obj N ⟶ M) :
    (dgDerivedExtension R C D F).obj ((moduleToDerived R C).obj N) ⟶
      (moduleToDerived R D).obj M :=
  (dgDerivedExtensionResolutionComputation R C D F
    (moduleCanonicalProjectiveResolution R C N)).hom ≫
    (moduleToDerived R D).map
      ((dgModuleExtension R C D F).onClosed.map (moduleCanonicalProjectiveResolution R C N).π ≫ s)

set_option maxHeartbeats 2000000 in
-- 標準分解と元の射影的始域の二つの Hom 同値を照合するために必要。
/-- 概要：射影的始域では標準分解を介する導来比較の随伴像は通常随伴像の主局所化。
方針：指定導来 Hom 同値を展開し、射影的始域での自然性で標準増大を消去する。
規約：KST §3.1。使われ方：canonical な局所係数拡大比較の経路の同定。 -/
theorem canonicalResolutionExtensionComparison_adjunct
    (N : ModuleCategory R C) (hN : moduleHomotopicallyProjective R C N)
    (M : ModuleCategory R D) (s : (dgModuleExtension R C D F).onClosed.obj N ⟶ M) :
    (dgDerivedExtensionRestrictionAdjunction R C D F).homEquiv _ _
      (canonicalResolutionExtensionComparison R C D F N M s) =
      (moduleToDerived R C).map
        ((dgModuleEnrichedRestrictionAdjunction R C D F).homEquiv N M s) ≫
        (dgDerivedRestrictionComputation R C D F M).inv := by
  let P := moduleCanonicalProjectiveResolution R C N
  rw [dgDerivedExtensionRestrictionAdjunction_homEquiv]
  change dgDerivedExtensionHomEquivOnModules R C D F N M _ = _
  rw [dgDerivedExtensionHomEquivOnModules_apply]
  change (moduleDerivedIso R C P.π P.quasiIso).inv ≫
      dgProjectiveDerivedExtensionHomEquiv R C D F P.obj P.projective M
        ((dgDerivedExtensionResolutionComputation R C D F P).inv ≫
          ((dgDerivedExtensionResolutionComputation R C D F P).hom ≫
            (moduleToDerived R D).map ((dgModuleExtension R C D F).onClosed.map P.π ≫ s))) = _
  rw [Iso.inv_hom_id_assoc, CategoryTheory.Functor.map_comp,
    dgProjectiveDerivedExtensionHomEquiv_naturality_left R C D F P.obj N P.projective hN M P.π]
  change (moduleDerivedIso R C P.π P.quasiIso).inv ≫
      ((moduleDerivedIso R C P.π P.quasiIso).hom ≫
        dgProjectiveDerivedExtensionHomEquiv R C D F N hN M ((moduleToDerived R D).map s)) = _
  rw [Iso.inv_hom_id_assoc, dgProjectiveDerivedExtensionHomEquiv_map]

/-- 概要：射影的始域の通常延長比較が同型なら、標準分解を介する導来比較も同型。
方針：射影的加群間の増大の graph 延長が擬同型になることを使う。
規約：KST §3.1。使われ方：局所 regular 加群の係数拡大比較の可逆性。 -/
theorem canonicalResolutionExtensionComparison_isIso
    (N : ModuleCategory R C) (hN : moduleHomotopicallyProjective R C N)
    (M : ModuleCategory R D) (s : (dgModuleExtension R C D F).onClosed.obj N ⟶ M) [IsIso s] :
    IsIso (canonicalResolutionExtensionComparison R C D F N M s) := by
  let P := moduleCanonicalProjectiveResolution R C N
  have hi : IsIso ((moduleToDerived R D).map ((dgModuleExtension R C D F).onClosed.map P.π)) :=
    moduleToDerived_inverts R D _
      (dgModuleExtension_projective_quasiIso R C D F P.projective hN P.π P.quasiIso)
  let := hi
  change IsIso ((dgDerivedExtensionResolutionComputation R C D F P).hom ≫
    (moduleToDerived R D).map ((dgModuleExtension R C D F).onClosed.map P.π ≫ s))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.KST.DerivedBlowup
