module

public import SerrePositivity.HomologicalAlgebra.KoszulRestriction
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution

/-!
# 環同型による Koszul 正則性の移送

## 概要
環同型は有限列の Koszul 分解の性質を保つ。
## 方針
係数制限後の実際の Koszul ホモロジーを比較する。
## 規約
非零性や正則な主元を仮定しない。
## 使われ方
BS 著者版 Proposition 7.10 の perfect prism の剰余表示。
-/

public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 環同型は、実際の Koszul 複体の正次数・負次数の消滅を保つ。 -/
theorem IsKoszulResolution.map_ringEquiv {r : ℕ} {z : Fin r → R}
    (hz : IsKoszulResolution z) (e : R ≃+* S) : IsKoszulResolution (e ∘ z) := by
  refine ⟨?_, koszulComplex_homology_zero_equiv _⟩
  intro i hi
  let e0 := ModuleCat.restrictScalarsIsoOfEquiv e
  let eK := (koszulModuleFunctor z).mapIso e0 ≪≫ eqToIso (koszulComplexOn_single z)
  have hK : IsZero (((koszulModuleFunctor z).obj
      ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S S))).homology i) :=
    (hz.isZero i hi).of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso eK)
  have h := hK.of_iso (koszulModuleHomologyIso e.toRingHom z i).symm
  have hSub := ModuleCat.subsingleton_of_isZero h
  change Subsingleton ((koszulComplex (e ∘ z)).homology i) at hSub
  exact ModuleCat.isZero_iff_subsingleton.mpr hSub

end SerrePositivity
