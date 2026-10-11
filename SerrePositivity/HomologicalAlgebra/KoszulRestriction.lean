module

public import SerrePositivity.HomologicalAlgebra.KoszulDirectedLimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # 係数加群による Koszul 複体と係数制限

代数を底環上の加群として Koszul 構成に入れると、代数上の Koszul 複体を
底環へ係数制限したものになる。近似環を同じ加群圏の図式として扱うための同型。
さらに別の環へ係数制限したホモロジーの比較も与える。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {S B : Type u} [CommRing S] [CommRing B] (β : S →+* B)

/-- 係数制限は、像の元によるスカラー作用を元の元の作用へ戻す。 -/
lemma restrictScalars_smulId (P : CochainComplex (ModuleCat.{u} B) ℤ) (a : S) :
    ((ModuleCat.restrictScalars β).mapHomologicalComplex (.up ℤ)).map (smulId (β a) P) =
      smulId a (((ModuleCat.restrictScalars β).mapHomologicalComplex (.up ℤ)).obj P) := by
  ext i x
  rfl

/-- 代数を係数加群とする Koszul 複体は、代数上の Koszul 複体の係数制限と同型。 -/
noncomputable def koszulModuleRestrictIso : ∀ {r : ℕ} (z : Fin r → S),
    (koszulModuleFunctor z).obj ((ModuleCat.restrictScalars β).obj (ModuleCat.of B B)) ≅
      ((ModuleCat.restrictScalars β).mapHomologicalComplex (.up ℤ)).obj
        (koszulComplex (β ∘ z))
  | 0, _ =>
      ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars β)
        (c := ComplexShape.up ℤ) 0).app (ModuleCat.of B B)).symm
  | r + 1, z => by
      refine (scalarConeFunctor (z (Fin.last r))).mapIso
        (koszulModuleRestrictIso (Fin.init z)) ≪≫ ?_
      refine ?_ ≪≫ (CochainComplex.mappingCone.mapHomologicalComplexIso
        (smulId (β (z (Fin.last r))) (koszulComplex (β ∘ Fin.init z)))
        (ModuleCat.restrictScalars β)).symm
      rw [restrictScalars_smulId]
      exact Iso.refl _

/-- 係数加群による構成のホモロジーを、代数上の Koszul ホモロジーに戻す。 -/
noncomputable def koszulModuleHomologyIso {r : ℕ} (z : Fin r → S) (i : ℤ) :
    ((koszulModuleFunctor z).obj
      ((ModuleCat.restrictScalars β).obj (ModuleCat.of B B))).homology i ≅
        (ModuleCat.restrictScalars β).obj ((koszulComplex (β ∘ z)).homology i) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso (koszulModuleRestrictIso β z) ≪≫
    ((koszulComplex (β ∘ z)).sc i).mapHomologyIso (ModuleCat.restrictScalars β)

variable {R : Type u} [CommRing R] (φ : R →+* S)

/-- 二段の係数制限を含むホモロジーの同型。長さを測る環 `R` 上で比較する。 -/
noncomputable def koszulModuleRestrictedHomologyIso {r : ℕ} (z : Fin r → S) (i : ℤ) :
    (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
      ((koszulModuleFunctor z).obj
        ((ModuleCat.restrictScalars β).obj (ModuleCat.of B B)))).homology i ≅
      (ModuleCat.restrictScalars (β.comp φ)).obj ((koszulComplex (β ∘ z)).homology i) :=
  (((koszulModuleFunctor z).obj
    ((ModuleCat.restrictScalars β).obj (ModuleCat.of B B))).sc i).mapHomologyIso
      (ModuleCat.restrictScalars φ) ≪≫
    (ModuleCat.restrictScalars φ).mapIso (koszulModuleHomologyIso β z i) ≪≫
    (ModuleCat.restrictScalarsComp'App φ β (β.comp φ) rfl
      ((koszulComplex (β ∘ z)).homology i)).symm

end SerrePositivity
