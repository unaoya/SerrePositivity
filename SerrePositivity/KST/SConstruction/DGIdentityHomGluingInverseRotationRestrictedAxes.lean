module
public import SerrePositivity.KST.SConstruction.DGIdentityInverseRotationModuleAxes
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingShiftedLeftAxis
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingConeFamilyInclusion

/-!
概要：元実逆回転二実像の全評価軸を元厳密比較の始域へ回収する。
方針：元全軸等号を前合成し同じ全 cone・shift 族へ接続する。
規約：元始域・元全 Hom・指定 shift を保持する。
使われ方：元実 gluing cone 全 realization 比較と同じ全実逆回転比較の接続。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma shiftedRecovery {R : Type u} [CommRing R] {E : Type v}
    [DGCategory R E] [Small.{u} E] {P : Type w} [DGCategory R P]
    {L : Type z} [DGCategory R L] (H : DGFunctor R P L)
    (F : DGFunctor R L (RightModule R E)) (B : DGFunctor R P (RightModule R E))
    (S : DGFunctor R (RightModule R E) (RightModule R E)) (h : H.comp F = B) :
    H.comp (F.comp S) = B.comp S :=
  (strictDGFunctor_comp_assoc H F S).symm.trans (congrArg (fun T => T.comp S) h)
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  {P : Type (max (u + 1) v)} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "I" => DGFunctor.id C
local notation "M" => dgHomGluingBimodule R C C C (I) (I)
local notation "H" => dgIdentityHomGluingFunctor R C F G a h

local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C C (M)
local notation "family" => dgHomGluingLoopConeFamily R C C C (I) (I)
local notation "J" => dgSmallPerfectEnvelopeInclusion R C ((L) ⊕ (L)) (family)
local notation "K" => dgPerfectModuleUnderlying R C (J)
local notation "Loop" => dgHomGluingLoopConeSmall R C C C (I) (I)
local notation "DS" => dgHomGluingLoopConeShiftedTarget R C C C (I) (I)
local notation "B" => dgIdentityHomGluingModuleConeFamily R C F G a h
local notation "FS" => DGFunctor.comp (F.comp (dgYoneda R C)) (moduleShiftDG R C 1)
local notation "S" => moduleShiftDG R C (-1)

/-- 概要：元始域上の逆回転実像左軸は同じ元実 cone の逆 shift。
方針：元全二軸回収を前合成し同じ実 cone 族へ戻す。
規約：元全関手の等号。使われ方：実逆回転入力 cone の始域回収。 -/
lemma dgIdentityHomGluingInverseRotationImageSource_restriction :
    (H).comp ((Loop).comp (K)) = (B).comp (S) := by
  exact (congrArg (fun T => (H).comp T) (dgIdentityInverseRotationImageSource_shift R C)).trans
    (shiftedRecovery (H) (dgHomGluingModuleConeFunctor R C C C (I) (I)) (B) (S)
      (dgIdentityHomGluingModuleConeFamily_inclusion R C F G a h).symm)

/-- 概要：元始域上の逆回転実像右軸は同じ元左 Yoneda 族の指定二重 shift。
方針：元全二軸回収を前合成し元 shifted 左軸を回収する。
規約：元全関手の等号。使われ方：元指定相殺を保つ実逆回転入力回収。 -/
lemma dgIdentityHomGluingInverseRotationImageTarget_restriction :
    (H).comp ((DS).comp (K)) = (FS).comp (S) := by
  exact (congrArg (fun T => (H).comp T) (dgIdentityInverseRotationImageTarget_shift R C)).trans
    (shiftedRecovery (H) (dgHomGluingShiftedLeftModuleFunctor R C C C (I) (I)) (FS) (S)
      (dgIdentityHomGluingShiftedLeftAxis R C F G a h))
end SerrePositivity.KST.SConstruction
