module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.ArityRepresentationAugmentation
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# 実際の arity の射影解像度

## 概要
HA 3.2.4.7 の二色比較に使う、Barratt–Eccles の arity の射影解像度を与える。

## 方針
指定された増大の忘却を元の正規化鎖の収縮と比較し、擬同型性を表現の圏へ反映する。

## 規約
増大は既存の `complexAugmentation` から作った射のまま保持する。

## 使われ方
二色部分群への制限と、指定された比較射の同変な鎖ホモトピー逆。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 指定増大の忘却は、元の正規化鎖の収縮の順射と一致する。 -/
lemma arityRepresentationAugmentation_forget (n : ℕ) :
    let U := forget₂ (Rep.{u} A (ULift.{u} (Equiv.Perm (Fin n)))) (ModuleCat.{u} A)
    let T := Rep.trivial A (ULift.{u} (Equiv.Perm (Fin n))) (𝟙_ (ModuleCat A))
    (U.mapHomologicalComplex (.down ℕ)).map (arityRepresentationAugmentation A n) ≫
      (singleMapHomologicalComplex U (.down ℕ) 0).hom.app T =
      (arityRepresentationChainForgetIso A n).hom ≫ (normalizedChainContraction A n).hom := by
  dsimp only
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f]
  change (forget₂ (Rep.{u} A (ULift.{u} (Equiv.Perm (Fin n)))) (ModuleCat.{u} A)).map
    ((arityRepresentationAugmentation A n).f 0) ≫ _ =
    (complexXIso A n 0).hom ≫ (normalizedChainContraction A n).hom.f 0
  rw [arityRepresentationAugmentation_f_zero, singleMapHomologicalComplex_hom_app_self]
  simp only [singleObjXSelf, singleObjXIsoOfEq]
  apply (cancel_epi (complexXIso A n 0).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  ext w
  exact complexAugmentation_zero_apply A n w

/-- 実際の表現の増大は、任意の可換基礎環で擬同型となる。 -/
lemma arityRepresentationAugmentation_quasiIso (n : ℕ) :
    QuasiIso (arityRepresentationAugmentation A n) := by
  let U := forget₂ (Rep.{u} A (ULift.{u} (Equiv.Perm (Fin n)))) (ModuleCat.{u} A)
  let T := Rep.trivial A (ULift.{u} (Equiv.Perm (Fin n))) (𝟙_ (ModuleCat A))
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (arityRepresentationAugmentation A n) U]
  apply (quasiIso_iff_comp_right _ ((singleMapHomologicalComplex U (.down ℕ) 0).hom.app T)).mp
  rw [arityRepresentationAugmentation_forget]
  have : QuasiIso (normalizedChainContraction A n).hom :=
    HomotopyEquiv.quasiIso_hom (normalizedChainContraction A n)
  infer_instance

/-- 実際の arity の鎖複体と指定増大からなる射影解像度。 -/
def arityProjectiveResolution (n : ℕ) :
    ProjectiveResolution (Rep.trivial A (ULift.{u} (Equiv.Perm (Fin n))) (𝟙_ (ModuleCat A))) where
  complex := arityRepresentationChain A n
  projective := arityRepresentationChain_projective A n
  π := arityRepresentationAugmentation A n
  quasiIso := arityRepresentationAugmentation_quasiIso A n

end SerrePositivity.EInfinity.BarrattEccles
