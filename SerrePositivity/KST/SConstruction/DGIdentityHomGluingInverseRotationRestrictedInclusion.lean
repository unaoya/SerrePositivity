module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationRestrictedInput
public import SerrePositivity.KST.SConstruction.DGIdentityInverseRotationRealizedConeBoundary
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeInrTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNerveWhiskerHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransNerveHomTransport

/-!
概要：元実逆回転全評価の右包含を元始域の同じ connecting cone 包含へ回収する。
方針：元二軸・元入力射・全 cone 族の回収と同じ閉成分を照合する。
規約：元実包含を新たな辺に置き換えない。
使われ方：元全評価比較と元指定上二単体の合成。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma nervePrecompRecovery
    (A : Type u) [CommRing A] (E : Type v) [DGCategory A E] [Small.{u} E]
    (X Y : Type (max (u + 1) v)) [DGCategory A X] [DGCategory A Y]
    (F0 G0 : DGFunctor A X (RightModule A E)) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F0 G0)
    (H0 : DGFunctor A Y X) (F1 G1 : DGFunctor A Y (RightModule A E))
    (t1 : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F1 G1) (hF : H0.comp F0 = F1) (hG : H0.comp G0 = G1)
    (ht : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp H0 t) t1) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H0)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom A X (RightModule A E) t))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom A Y (RightModule A E) t1) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_precomp_heq A Y X (RightModule A E) H0 t
  have hi := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_heq A Y (RightModule A E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp H0 t) t1 hF hG ht
  exact hp.symm.trans hi

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

local notation "η" => dgIdentityInverseRotationImageComparison R C
local notation "β" => dgIdentityHomGluingConeConnectingComparison R C F G a h
local notation "βs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (β) (S)

local notation "F0" => DGFunctor.comp (Loop) (K)
local notation "G0" => DGFunctor.comp (DS) (K)
local notation "CI" => dgIdentityInverseRotationImageConeFamily R C
local notation "GI" => dgIdentityInverseRotationImageConeInr R C
local notation "MI" => dgIdentityHomGluingInverseRotationModuleSource R C F G a h
local notation "LI" => dgModuleNaturalConeInr R C (DGFunctor.comp (B) (S)) (DGFunctor.comp (FS) (S)) (βs)

/-- 概要：元実逆回転像 cone の包含制限は元 connecting cone の同じ包含。
方針：元二軸と入力射の全回収を元閉成分の外延性へ渡す。
規約：全厳密比較の型付き一致。使われ方：元実全比較と元上二単体の接続。 -/
lemma dgIdentityHomGluingInverseRotationImageConeInr_restriction :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp (H) (GI)) (LI) := by
  exact (dgModuleNaturalConeInr_precomp_heq R C (F0) (G0) (η) (H)).trans
    (dgModuleNaturalConeInr_heq R C ((H).comp (F0)) ((H).comp (G0))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp (H) (η)) (DGFunctor.comp (B) (S)) (DGFunctor.comp (FS) (S)) (βs)
      (dgIdentityHomGluingInverseRotationImageSource_restriction R C F G a h)
      (dgIdentityHomGluingInverseRotationImageTarget_restriction R C F G a h)
      (dgIdentityHomGluingInverseRotationImageComparison_restriction R C F G a h))

/-- 概要：元全実逆回転の包含を元 native 始域へ制限しても同じ元包含の射。
方針：同じ厳密前合成の nerve 整合性と元全包含の型付き回収を使う。
規約：全関手射を保持。使われ方：元実評価の native 包含境界を元上二単体へ移す。 -/
lemma dgIdentityHomGluingInverseRotationImageConeInr_nerve_restriction :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (G0)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CI)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (L) (RightModule R C) (GI)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (LI)) := by
  exact nervePrecompRecovery R C (L) P (G0) (CI) (GI) (H)
    (DGFunctor.comp (FS) (S)) (MI) (LI)
    (dgIdentityHomGluingInverseRotationImageTarget_restriction R C F G a h)
    (dgIdentityHomGluingInverseRotationImageConeFamily_restriction R C F G a h)
    (dgIdentityHomGluingInverseRotationImageConeInr_restriction R C F G a h)
end SerrePositivity.KST.SConstruction
