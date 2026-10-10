module

public import SerrePositivity.HomologicalAlgebra.Tor
public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # 環自己同型による係数変更とホモロジーの長さ

係数拡大と逆自己同型による係数制限を比較する。
通常長さの不変性は任意の複体・全次数の Tor に成り立ち、有限性や有界性を要求しない。
-/

@[expose] public section

universe u

namespace SerrePositivity

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

variable {R T C : Type u} [CommRing R] [CommRing T] [CommRing C]

/-- 二段階の係数拡大 `(F ⊗_R T) ⊗_T C` と一段階の係数拡大 `F ⊗_R C`（合成 `ψ ∘ φ : R → C` に沿う）の
複体の同型。Mathlib の `ModuleCat.extendScalarsComp`（関手の合成の自然同型）を各項に施す。 -/
noncomputable def baseChangeCompIso (φ : R →+* T) (ψ : T →+* C)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    baseChange ψ (baseChange φ F) ≅ baseChange (ψ.comp φ) F :=
  (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp φ ψ).symm
    (ComplexShape.up ℤ)).app F

/-- 環自己同型 `σ` に沿った係数制限は、逆 `σ⁻¹` に沿った係数拡大と自然同型：`restrictScalars σ` は
圏同値で `restrictScalars σ⁻¹` の左随伴、一方 `extendScalars σ⁻¹` も `restrictScalars σ⁻¹` の左随伴
なので、左随伴の一意性（`Adjunction.leftAdjointUniq`）による。ノルム比較で群の添字に逆元が現れる
理由。 -/
noncomputable def restrictScalarsIsoExtendInverse (σ : T ≃+* T) :
    ModuleCat.restrictScalars.{u} σ.toRingHom ≅ ModuleCat.extendScalars σ.symm.toRingHom :=
  Adjunction.leftAdjointUniq (ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).toAdjunction
    (ModuleCat.extendRestrictScalarsAdj σ.symm.toRingHom)

/-- 自己同型に沿う係数拡大は、各次数のホモロジーの通常長さを保つ。 -/
lemma length_homology_baseChange_equiv (σ : T ≃+* T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ) (q : ℤ) :
    Module.length T ((baseChange σ.toRingHom P).homology q) =
      Module.length T (P.homology q) := by
  let F := ModuleCat.restrictScalars.{u} σ.symm.toRingHom
  let e := ((NatIso.mapHomologicalComplex (restrictScalarsIsoExtendInverse σ.symm)
    (.up ℤ)).app P).symm
  have he := ((HomologicalComplex.homologyFunctor _ _ q).mapIso e).toLinearEquiv.length_eq
  have hf := ((P.sc q).mapHomologyIso F).toLinearEquiv.length_eq
  exact he.trans (hf.trans (length_restrictScalars_equiv σ.symm _))

/-- 係数代数の構造写像を自己同型でひねっても、Tor の通常長さは変わらない。 -/
lemma length_torAlg_comp_equiv (φ : R →+* T) (σ : T ≃+* T)
    (M : Type u) [AddCommGroup M] [Module R M] (i : ℕ) :
    Module.length T (TorAlg (σ.toRingHom.comp φ) i M) =
      Module.length T (TorAlg φ i M) := by
  let P := extRes (projectiveResolution (ModuleCat.of R M))
  let hP := isResolutionOf_extRes (projectiveResolution (ModuleCat.of R M))
  rw [(torIsoCochain (σ.toRingHom.comp φ) hP i).toLinearEquiv.length_eq,
    (torIsoCochain φ hP i).toLinearEquiv.length_eq]
  exact (((HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso
    (baseChangeCompIso φ σ.toRingHom P)).toLinearEquiv.length_eq).symm.trans
      (length_homology_baseChange_equiv σ (baseChange φ P) _)

end SerrePositivity
