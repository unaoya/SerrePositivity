module
public import SerrePositivity.KST.SConstruction.DGHomGluingLoopCone
public import SerrePositivity.KST.SConstruction.DGHomGluingConeConnectingComparison
public import SerrePositivity.KST.SConstruction.DGClosedComparisonPostcomposition
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingFunctor
public import SerrePositivity.KST.SConstruction.DGHomGluingLoopConeModuleMaps
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeClosedComparison

/-!
概要：元 Hom gluing の cone 逆回転を二実像小模型上の厳密 Hom gluing 関手で構成する。
方針：元 connecting 比較を真の dg 逆 shift で後合成し、同じ全 Hom 自然性を使う。
規約：指定二重 shift と全第三成分を保持。使われ方：LT の共通実長方形の中央比較。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)
local notation "T" => DGHomGluingLoopConeBase R C D E p q

/-- 概要：元実 cone の逆 shift から元左対象の二重 shift への同じ加群閉射。
方針：元 connecting 射を真の dg 逆 shift で写す。
規約：同じ実二対象を保持。使われ方：全自然性の元加群表示。 -/
def dgHomGluingInverseRotationModuleMap (X : L) :
    ForgetEnrichment.of (Complex R) ((dgHomGluingLoopConeFunctor R C D E p q).obj X).val ⟶
      ForgetEnrichment.of (Complex R)
        ((dgHomGluingDoubleShiftLeftFunctor R C D E p q).obj X).val :=
  (moduleShiftDG R E (-1)).onClosed.map
    (moduleConeConnecting R E (dgHomGluingTargetModuleMap R C D E p q X))

/-- 概要：元加群内の逆回転射は同じ全 Hom 作用に関して自然。
方針：元 connecting 比較の全 dg 後合成と同じ全 Hom 回収式を使う。
規約：元第三 cochain と指定 shift を保持。使われ方：共通小模型への自然性輸送。 -/
lemma dgHomGluingInverseRotation_module_naturality (X Y : L) :
    (dgHomGluingLoopConeFunctor R C D E p q).map X Y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) ((dgHomGluingLoopConeFunctor R C D E p q).obj X).val)
        (dgHomGluingInverseRotationModuleMap R C D E p q Y) =
    (dgHomGluingDoubleShiftLeftFunctor R C D E p q).map X Y ≫
      eHomWhiskerRight (Complex R) (dgHomGluingInverseRotationModuleMap R C D E p q X)
        (ForgetEnrichment.of (Complex R)
          ((dgHomGluingDoubleShiftLeftFunctor R C D E p q).obj Y).val) := by
  have h := dgClosedComparison_postcomp_naturality R
    (dgHomGluingModuleConeFunctor R C D E p q)
    (dgHomGluingShiftedLeftModuleFunctor R C D E p q) (moduleShiftDG R E (-1))
    (fun X => moduleConeConnecting R E (dgHomGluingTargetModuleMap R C D E p q X))
    (dgHomGluingConeConnecting_hom_naturality R C D E p q) X Y
  exact (congrArg (fun k => k ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) ((dgHomGluingLoopConeFunctor R C D E p q).obj X).val)
      (dgHomGluingInverseRotationModuleMap R C D E p q Y))
    (dgHomGluingLoopConeFunctor_module_map R C D E p q X Y)).trans
      (h.trans (congrArg (fun k => k ≫ eHomWhiskerRight (Complex R)
        (dgHomGluingInverseRotationModuleMap R C D E p q X)
        (ForgetEnrichment.of (Complex R)
          ((dgHomGluingDoubleShiftLeftFunctor R C D E p q).obj Y).val))
        (dgHomGluingDoubleShiftLeftFunctor_module_map R C D E p q X Y)).symm)

/-- 概要：同じ元加群の逆回転射を二実像小模型の閉射として保持する。
方針：元の閉射を同じ充満 Hom 内で使う。
規約：対象・射を変更しない。使われ方：実 Hom gluing 関手の比較成分。 -/
def dgHomGluingInverseRotationMap (X : L) :
    ForgetEnrichment.of (Complex R) ((dgHomGluingLoopConeSmall R C D E p q).obj X) ⟶
      ForgetEnrichment.of (Complex R) ((dgHomGluingLoopConeShiftedTarget R C D E p q).obj X) :=
  dgSmallPerfectEnvelopeComparisonMap R E ((L) ⊕ (L))
    (dgHomGluingLoopConeFamily R C D E p q)
    (dgHomGluingLoopConeFunctor R C D E p q) (dgHomGluingDoubleShiftLeftFunctor R C D E p q)
    Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl)
    (dgHomGluingInverseRotationModuleMap R C D E p q) X

/-- 概要：同じ小模型内の逆回転射は元全 Hom に関して自然。
方針：全実像を保つ制限の抽象補題へ同じ元加群自然性を渡す。
規約：元第三 cochain と全 shift を保持。使われ方：逆回転の厳密 Hom gluing 関手。 -/
lemma dgHomGluingInverseRotationMap_hom_naturality (X Y : L) :
    (dgHomGluingLoopConeSmall R C D E p q).map X Y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) ((dgHomGluingLoopConeSmall R C D E p q).obj X))
        (dgHomGluingInverseRotationMap R C D E p q Y) =
    (dgHomGluingLoopConeShiftedTarget R C D E p q).map X Y ≫
      eHomWhiskerRight (Complex R) (dgHomGluingInverseRotationMap R C D E p q X)
        (ForgetEnrichment.of (Complex R)
          ((dgHomGluingLoopConeShiftedTarget R C D E p q).obj Y)) :=
  dgSmallPerfectEnvelopeFunctorLift_comparison_naturality R E ((L) ⊕ (L))
    (dgHomGluingLoopConeFamily R C D E p q)
    (dgHomGluingLoopConeFunctor R C D E p q) (dgHomGluingDoubleShiftLeftFunctor R C D E p q)
    Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl)
    (dgHomGluingInverseRotationModuleMap R C D E p q)
    (dgHomGluingInverseRotation_module_naturality R C D E p q) X Y

/-- 概要：元三成分 cone の実逆回転を同じ小基底の恒等 Hom gluing へ送る。
方針：構成済み二成分と全 Hom 自然な元閉比較を厳密 Hom gluing 関手へ束ねる。
規約：元全対象・全 Hom を保持。使われ方：LT 実長方形の中央比較の構成部品。 -/
def dgHomGluingInverseRotationFunctor : DGFunctor R (L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R (T) (T)
      (dgHomGluingBimodule R (T) (T) (T) (DGFunctor.id (T)) (DGFunctor.id (T)))) :=
  dgIdentityHomGluingFunctor R (T)
    (dgHomGluingLoopConeSmall R C D E p q) (dgHomGluingLoopConeShiftedTarget R C D E p q)
    (dgHomGluingInverseRotationMap R C D E p q)
    (dgHomGluingInverseRotationMap_hom_naturality R C D E p q)
end SerrePositivity.KST.SConstruction
