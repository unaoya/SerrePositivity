module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.ArityRepresentationChain
public import SerrePositivity.EInfinity.BarrattEccles.AugmentationCochainValues
public import SerrePositivity.EInfinity.BarrattEccles.AugmentationNaturality
public import Mathlib.Algebra.Homology.Single

/-!
# 表現の圏の arity の増大

## 概要
HA 3.2.4.7 の二色比較のため、実際の Barratt–Eccles の増大を表現の射にする。

## 方針
零次成分の増大の不変性と微分との可換性を使い、単一成分複体への射を構成する。

## 規約
順方向の増大は既存の `complexAugmentation` の零次成分を保つ。

## 使われ方
Arity の射影解像度と、二色比較の増大の可換性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 実際の零次の増大を、自明表現への射として読む。 -/
def arityRepresentationAugmentationZero (n : ℕ) :
    (arityRepresentationChain A n).X 0 ⟶
      Rep.trivial A (ULift.{u} (Equiv.Perm (Fin n))) (𝟙_ (ModuleCat A)) :=
  Rep.ofHom ⟨((complexAugmentation A n).f 0 ≫
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom).hom, fun g => by
      change (((complexRightAction A n g.down⁻¹).f 0) ≫ (complexAugmentation A n).f 0 ≫
        (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom).hom =
        ((complexAugmentation A n).f 0 ≫
          (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom).hom
      have h := congrArg (fun f => f.f (0 : ℤ) ≫
        (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom)
        (complexRightAction_augmentation A n g.down⁻¹)
      exact congrArg ModuleCat.Hom.hom (by
        simpa only [HomologicalComplex.comp_f, Category.assoc] using h)⟩

/-- 表現の圏の零次の増大は前の微分を消す。 -/
lemma arityRepresentationAugmentationZero_d (n : ℕ) :
    (arityRepresentationChain A n).d 1 0 ≫ arityRepresentationAugmentationZero A n = 0 := by
  apply (forget₂ (Rep.{u} A (ULift.{u} (Equiv.Perm (Fin n)))) (ModuleCat.{u} A)).map_injective
  change (complex A n).d (-1) 0 ≫ ((complexAugmentation A n).f 0 ≫
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom) = 0
  rw [← Category.assoc, ← (complexAugmentation A n).comm (-1) 0]
  simp only [HomologicalComplex.single_obj_d, comp_zero, zero_comp]

/-- 表現の圏の arity の指定された鎖複体の増大。 -/
def arityRepresentationAugmentation (n : ℕ) :
    arityRepresentationChain A n ⟶
      (ChainComplex.single₀ (Rep.{u} A (ULift.{u} (Equiv.Perm (Fin n))))).obj
        (Rep.trivial A (ULift.{u} (Equiv.Perm (Fin n))) (𝟙_ (ModuleCat A))) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨arityRepresentationAugmentationZero A n, arityRepresentationAugmentationZero_d A n⟩

/-- 指定された鎖複体の増大は零次で元の増大と一致する。 -/
@[simp]
lemma arityRepresentationAugmentation_f_zero (n : ℕ) :
    (arityRepresentationAugmentation A n).f 0 = arityRepresentationAugmentationZero A n :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- Arity の表現の鎖複体の忘却と、元の正規化鎖との指定された比較。 -/
def arityRepresentationChainForgetIso (n : ℕ) :
    ((forget₂ (Rep.{u} A (ULift.{u} (Equiv.Perm (Fin n)))) (ModuleCat.{u} A)).mapHomologicalComplex
      (.down ℕ)).obj (arityRepresentationChain A n) ≅ normalizedChains A n :=
  HomologicalComplex.Hom.isoOfComponents (fun q => complexXIso A n q) (by
    intro i j h
    change ((normalizedChains A n).extendXIso ComplexShape.embeddingDownNat
      (i := i) (i' := -(i : ℤ)) rfl).hom ≫
      (normalizedChains A n).d i j =
        ((normalizedChains A n).extend ComplexShape.embeddingDownNat).d (-(i : ℤ)) (-(j : ℤ)) ≫
          ((normalizedChains A n).extendXIso ComplexShape.embeddingDownNat
            (i := j) (i' := -(j : ℤ)) rfl).hom
    rw [(normalizedChains A n).extend_d_eq ComplexShape.embeddingDownNat
      (i := i) (j := j) (i' := -(i : ℤ)) (j' := -(j : ℤ)) rfl rfl]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

end SerrePositivity.EInfinity.BarrattEccles
