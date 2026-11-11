module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationInv
public import SerrePositivity.DifferentialGraded.Module.ConeRotation

/-!
概要：全厳密回転逆の元閉射を従来の実回転逆と照合する。
方針：同じ右包含の厳密回収だけで cone の入力を輸送し、元 descent 射を回収する。
規約：元比較を成分ごと選び直さない。使われ方：実合成比較の同値成分認証。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
private lemma zeroDescCongr {M N T : ModuleCategory R D}
    (f g : M ⟶ N) (b c : N ⟶ T) (ef : f = g) (eb : b = c)
    (hf : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) T)).d (-1) 0 0 =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (f ≫ b))).val)
    (hg : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) T)).d (-1) 0 0 =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (g ≫ c))).val) :
    moduleConeDescOfBoundary R D f 0 b hf =
      (eqToIso (congrArg (fun t => moduleCone R D t) ef)).hom ≫
        moduleConeDescOfBoundary R D g 0 c hg := by
  cases ef
  cases eb
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]

private lemma isIsoMapOfEqComposite {A B C : ModuleCategory R D}
    (f : A ⟶ C) (e : A ≅ B) (g : B ⟶ C) (hf : f = e.hom ≫ g)
    (hg : IsIso ((moduleToHomotopy R D).map g)) : IsIso ((moduleToHomotopy R D).map f) := by
  letI := hg
  rw [hf, CategoryTheory.Functor.map_comp]
  infer_instance

variable {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "a" => dgModuleNaturalConeArrow R D F G η
local notation "T" => dgModuleNaturalConeFunctor R D F G η
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "δ" => dgModuleNaturalConeConnecting R D F G η
local notation "U" => dgModuleNaturalConeFunctor R D G (T) (ν)

/-- 概要：全族の二重 cone と元右包含の同じ二重 cone の指定実同型。
方針：同じ右包含回収等号だけで輸送する。
規約：同型対象を選び直さない。使われ方：元回転逆の始域の照合。 -/
def dgModuleNaturalConeRotationInvInputIso (x : P) :
    ForgetEnrichment.of (Complex R) ((U).obj x) ≅
      moduleCone R D (moduleConeInr R D (a x)) :=
  eqToIso (congrArg (fun t => moduleCone R D t) (dgModuleNaturalConeInr_arrow R D F G η x))

/-- 概要：全厳密回転逆の成分は同じ元実回転逆を入力輸送した射そのもの。
方針：元 descent 射と指定右包含・connecting の回収を使用する。
規約：成分の可逆性だけで全自然性を代用しない。使われ方：全族と元の同値判定の接続。 -/
lemma dgModuleNaturalConeRotationInv_arrow_eq (x : P) :
    dgModuleNaturalConeArrow R D (U) (F.comp (moduleShiftDG R D 1))
      (dgModuleNaturalConeRotationInv R D F G η) x =
      (dgModuleNaturalConeRotationInvInputIso R D F G η x).hom ≫
        moduleConeRotationInv R D (a x) := by
  have ha := dgModuleNaturalConeDesc_arrow R D G (T) (F.comp (moduleShiftDG R D 1))
    (ν) (δ) (fun _ => 0) (dgModuleNaturalConeRotationInv_boundary R D F G η)
    (by intro x y n z; simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, smul_zero]) x
  apply ha.trans
  exact zeroDescCongr R D _ _ _ _
    (dgModuleNaturalConeInr_arrow R D F G η x)
    (dgModuleNaturalConeConnecting_arrow R D F G η x)
    (dgModuleNaturalConeRotationInv_boundary R D F G η x)
    (moduleConeRotationInv_condition R D (a x))

/-- 概要：同じ全厳密回転逆は各成分で元加群ホモトピー圏の同値。
方針：元の指定入力同型と実回転逆の同値を合成する。
規約：全自然性は前段で実証済み。使われ方：native 全比較の可逆性。 -/
lemma dgModuleNaturalConeRotationInv_isIso (x : P) :
    IsIso ((moduleToHomotopy R D).map
      (dgModuleNaturalConeArrow R D (U) (F.comp (moduleShiftDG R D 1))
        (dgModuleNaturalConeRotationInv R D F G η) x)) := by
  exact isIsoMapOfEqComposite R D _ (dgModuleNaturalConeRotationInvInputIso R D F G η x)
    (moduleConeRotationInv R D (a x)) (dgModuleNaturalConeRotationInv_arrow_eq R D F G η x)
    (moduleConeRotationHomotopyIso R D (a x)).isIso_inv
end SerrePositivity.KST.SConstruction
