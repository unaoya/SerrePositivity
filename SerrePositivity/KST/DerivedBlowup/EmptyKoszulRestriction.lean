module

public import SerrePositivity.KST.DerivedBlowup.ExteriorAugmentationDGFunctor

/-!
概要：KST Def3.1 の空 Koszul dg 模型の係数制限を通常の単一複体に同定する。
方針：空列の単位同型と係数制限の single 比較を合成する。
規約：係数環 S を R 上の代数として読む。
使われ方：標準添加 dg 関手と明示的な添加鎖写像の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded.ScalarExtension

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 概要：係数制限した空 Koszul Hom 複体と S の次数0単一複体との同型。
方針：空列の単位同型を係数制限し、single と係数制限の比較を合成する。
規約：KST Def3.1。使われ方：標準添加の dg 関手と鎖写像の接続。 -/
def emptyKoszulRestrictionIso (φ : R →+* S) :
    letI := φ.toAlgebra
    (restriction φ).obj (sequenceExteriorCochain (Fin.elim0 : Fin 0 → S)) ≅
      (single _ (ComplexShape.up ℤ) 0).obj (ModuleCat.of R S) := by
  letI := φ.toAlgebra
  exact (restriction φ).mapIso (sequenceExteriorCochain_empty_iso Fin.elim0).symm ≪≫
    (singleMapHomologicalComplex (ModuleCat.restrictScalars φ) (.up ℤ) 0).app _

/-- 概要：係数制限した空 Koszul dg 圏の単位を比較同型で送ると係数制限の単位になる。
方針：係数制限の単位公式と空列の単位同型の逆を合成する。
規約：KST Def3.1。使われ方：添加 dg 関手の次数0での1保存。 -/
theorem emptyKoszulRestriction_unit (φ : R →+* S) :
    letI := φ.toAlgebra
    eId (DifferentialGraded.Complex R)
        (C := DGRestriction φ (EmptyKoszulObject S)) (ExteriorKoszulObject.point) ≫
      (emptyKoszulRestrictionIso φ).hom =
        Functor.LaxMonoidal.ε (restriction φ) ≫
          ((singleMapHomologicalComplex (ModuleCat.restrictScalars φ) (.up ℤ) 0).app
            (ModuleCat.of S S)).hom := by
  let := φ.toAlgebra
  change (Functor.LaxMonoidal.ε (restriction φ) ≫
    (restriction φ).map (exteriorKoszulUnit
      (Finsupp.linearCombination S (Fin.elim0 : Fin 0 → S)))) ≫ _ = _
  dsimp only [emptyKoszulRestrictionIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  have he : exteriorKoszulUnit (Finsupp.linearCombination S (Fin.elim0 : Fin 0 → S)) =
      (sequenceExteriorCochain_empty_iso (Fin.elim0 : Fin 0 → S)).hom := rfl
  rw [he, Iso.hom_inv_id]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp]

/-- 概要：空 Koszul 比較は dg 単位の1を通常の係数1へ送る。
方針：単位比較の式を次数0で評価し、係数制限の単位公式を使う。
規約：KST Def3.1。使われ方：標準添加鎖写像の一意性。 -/
theorem emptyKoszulRestriction_unit_one (φ : R →+* S) :
    letI := φ.toAlgebra
    ((eId (DifferentialGraded.Complex R)
      (C := DGRestriction φ (EmptyKoszulObject S)) (ExteriorKoszulObject.point) ≫
        (emptyKoszulRestrictionIso φ).hom).f 0)
      ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).inv (1 : R)) =
        (singleObjXSelf (.up ℤ) 0 (ModuleCat.of R S)).inv (1 : S) := by
  let := φ.toAlgebra
  rw [emptyKoszulRestriction_unit]
  change (((singleMapHomologicalComplex (ModuleCat.restrictScalars φ) (.up ℤ) 0).app
    (ModuleCat.of S S)).hom.f 0)
      (((Functor.LaxMonoidal.ε (restriction φ)).f 0)
        ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat R))).inv (1 : R))) = _
  rw [restriction_ε_one]
  erw [singleMapHomologicalComplex_hom_app_self]
  simp
  rfl

end SerrePositivity.KST.DerivedBlowup
