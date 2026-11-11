module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalInverseRotationCancellation

/-!
概要：同じ三因子からなる全実逆回転比較の成分同値を証明する。
方針：元 cone shift 同型、元全比較の shift 同値、元指定相殺を合成する。
規約：同じ元三因子の全厳密合成を保持する。
使われ方：全実逆回転の native 全関手同型。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type (max (u + 1) v)} [DGCategory R P]
private lemma strictCompositeIsIso
    (F G H : DGFunctor R P (RightModule R D))
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H) (x : P)
    (hf : IsIso ((moduleToHomotopy R D).map (dgModuleNaturalConeArrow R D F G η x)))
    (hg : IsIso ((moduleToHomotopy R D).map (dgModuleNaturalConeArrow R D G H θ x))) :
    IsIso ((moduleToHomotopy R D).map
      (dgModuleNaturalConeArrow R D F H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp η θ) x)) := by
  haveI := hf
  haveI := hg
  rw [dgModuleNaturalConeArrow_comp, CategoryTheory.Functor.map_comp]
  infer_instance
private lemma shiftedStrictIsIso (F G : DGFunctor R P (RightModule R D))
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (s : ℤ) (x : P)
    (hf : IsIso ((moduleToHomotopy R D).map (dgModuleNaturalConeArrow R D F G η x))) :
    IsIso ((moduleToHomotopy R D).map
      (dgModuleNaturalConeArrow R D (F.comp (moduleShiftDG R D s))
        (G.comp (moduleShiftDG R D s)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η (moduleShiftDG R D s)) x)) := by
  rw [dgModuleNaturalConeShiftArrow]
  exact dgModuleShiftMap_isIso R D _ s hf
variable (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "FS" => F.comp (moduleShiftDG R D 1)
local notation "GS" => G.comp (moduleShiftDG R D 1)
local notation "δ" => dgModuleNaturalConeConnecting R D F G η
local notation "CD" => dgModuleNaturalConeFunctor R D (CF) (FS) (δ)
local notation "S" => moduleShiftDG R D (-1)
local notation "L" => dgModuleNaturalInverseRotationSource R D F G η
local notation "α" => dgModuleNaturalInverseRotationConeShift R D F G η
local notation "β" => dgModuleNaturalInverseRotationShiftedComparison R D F G η
local notation "γ" => dgModuleNaturalInverseRotationCancellation R D G

/-- 概要：同じ元全実逆回転比較の各閉成分は K(D) の同値。
方針：同じ元三因子の同値を全厳密合成へ渡す。
規約：元指定成分・全比較を変更しない。使われ方：native 全実逆回転比較の可逆性。 -/
lemma dgModuleNaturalInverseRotation_isIso (x : P) :
    IsIso ((moduleToHomotopy R D).map
      (dgModuleNaturalConeArrow R D (L) G (dgModuleNaturalInverseRotation R D F G η) x)) := by
  have hα := dgModuleNaturalConeShiftComparison_isIso R D (CF) (FS) (δ) (-1) x
  have hβ := shiftedStrictIsIso R D (CD) (GS)
    (dgModuleNaturalConnectingConeComposite R D F G η) (-1) x
    (dgModuleNaturalConnectingConeComposite_isIso R D F G η x)
  have hγ : IsIso ((moduleToHomotopy R D).map
      (dgModuleNaturalConeArrow R D ((GS).comp (S)) G (γ) x)) :=
    (congrArg (fun k => IsIso ((moduleToHomotopy R D).map k))
      (dgModuleNaturalInverseRotationCancellation_arrow R D G x)).mpr
        (dgModuleSpecifiedCancellation_isIso R D (G.obj x))
  exact strictCompositeIsIso R D (L) ((GS).comp (S)) G
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (α) (β)) (γ) x
    (strictCompositeIsIso R D (L) ((CD).comp (S)) ((GS).comp (S)) (α) (β) x hα hβ) hγ
end SerrePositivity.KST.SConstruction
