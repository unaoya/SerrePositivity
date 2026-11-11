module
public import SerrePositivity.KST.SConstruction.DGIdentityInverseRotationRealization
public import SerrePositivity.KST.SConstruction.DGHomGluingLoopConeModuleMaps

/-!
概要：元実逆回転の実像二軸を同じ元全加群 cone と二重 shift へ回収する。
方針：元二実像の全包含回収と元全 Hom の module 表示を合成する。
規約：全関手の等号を保持する。
使われ方：元始域へ制限した connecting 逆 shift と同じ実 cone 入力の照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (E : Type (max (u + 1) v))
  [DGCategory R E] [Small.{u} E]
local notation "I" => DGFunctor.id E
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R E E (dgHomGluingBimodule R E E E (I) (I))
local notation "family" => dgHomGluingLoopConeFamily R E E E (I) (I)
local notation "J" => dgSmallPerfectEnvelopeInclusion R E ((L) ⊕ (L)) (family)
local notation "K" => dgPerfectModuleUnderlying R E (J)
local notation "F" => dgHomGluingLoopConeSmall R E E E (I) (I)
local notation "G" => dgHomGluingLoopConeShiftedTarget R E E E (I) (I)
local notation "S" => moduleShiftDG R E (-1)

/-- 概要：元実像左軸は同じ元全加群 cone の実逆 shift。
方針：全包含回収の後に元全 Hom の module 表示を適用する。
規約：元全鎖写像を保持。使われ方：元始域での全実逆回転入力左軸。 -/
lemma dgIdentityInverseRotationImageSource_shift :
    (F).comp (K) = (dgHomGluingModuleConeFunctor R E E E (I) (I)).comp (S) := by
  refine (dgIdentityInverseRotationImageSource R E).trans ?_
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  change (dgHomGluingLoopConeFunctor R E E E (I) (I)).map x y ≫ 𝟙 _ =
    ((dgHomGluingModuleConeFunctor R E E E (I) (I)).comp (S)).map x y
  exact (Category.comp_id _).trans (dgHomGluingLoopConeFunctor_module_map R E E E (I) (I) x y)

/-- 概要：元実像右軸は同じ元左 Yoneda 像の指定二重 shift。
方針：全包含回収の後に元二重 shift の全 Hom 表示を適用する。
規約：元二段 shift を保持。使われ方：指定相殺を保つ全実逆回転入力右軸。 -/
lemma dgIdentityInverseRotationImageTarget_shift :
    (G).comp (K) = (dgHomGluingShiftedLeftModuleFunctor R E E E (I) (I)).comp (S) := by
  refine (dgIdentityInverseRotationImageTarget R E).trans ?_
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  change (dgHomGluingDoubleShiftLeftFunctor R E E E (I) (I)).map x y ≫ 𝟙 _ =
    ((dgHomGluingShiftedLeftModuleFunctor R E E E (I) (I)).comp (S)).map x y
  exact (Category.comp_id _).trans
    (dgHomGluingDoubleShiftLeftFunctor_module_map R E E E (I) (I) x y)
end SerrePositivity.KST.SConstruction
