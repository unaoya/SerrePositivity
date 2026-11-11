module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationHom
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationInvComparison

/-!
概要：全厳密回転比較の元成分を従来の同じ実回転射と照合する。
方針：同じ cone 入力の回収で lift を輸送し、元 K(D) 同値を使う。
規約：元全比較と元の実射を保持。使われ方：同じ native 全回転比較の成分認証。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
private lemma liftCongr {M N T : ModuleCategory R D}
    (f g : M ⟶ N) (ef : f = g)
    (a : (moduleHom R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) M)).X 1)
    (b : (moduleHom R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) N)).X 0)
    (ha : (moduleHom R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) M)).d 1 2 a = 0)
    (hf : (moduleHom R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) N)).d 0 1 b +
      (show (moduleHom R D (ForgetEnrichment.to (Complex R) T)
        (ForgetEnrichment.to (Complex R) N)).X 1 from
        (eHomWhiskerLeft (Complex R) T f).f 1 a) = 0)
    (hg : (moduleHom R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) N)).d 0 1 b +
      (show (moduleHom R D (ForgetEnrichment.to (Complex R) T)
        (ForgetEnrichment.to (Complex R) N)).X 1 from
        (eHomWhiskerLeft (Complex R) T g).f 1 a) = 0) :
    moduleConeLiftOfCycle R D f a b ha hf ≫
      (eqToIso (congrArg (fun t => moduleCone R D t) ef)).hom =
        moduleConeLiftOfCycle R D g a b ha hg := by
  cases ef
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
private lemma isIsoMapOfPostIso {A B C : ModuleCategory R D}
    (f : A ⟶ B) (e : B ≅ C) (g : A ⟶ C) (hf : f ≫ e.hom = g)
    (hg : IsIso ((moduleToHomotopy R D).map g)) : IsIso ((moduleToHomotopy R D).map f) := by
  letI := hg
  haveI : IsIso ((moduleToHomotopy R D).map f ≫ (moduleToHomotopy R D).map e.hom) := by
    rw [← CategoryTheory.Functor.map_comp, hf]
    infer_instance
  exact IsIso.of_isIso_comp_right ((moduleToHomotopy R D).map f)
    ((moduleToHomotopy R D).map e.hom)

variable {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "a" => dgModuleNaturalConeArrow R D F G η
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "U" => dgModuleNaturalConeFunctor R D G (CF) (ν)
local notation "FS" => F.comp (moduleShiftDG R D 1)
local notation "γ" => dgModuleNaturalConeRotationHom R D F G η

/-- 概要：全厳密回転比較の同じ閉射は元二成分の実 cone lift。
方針：閉射・閉元対応の逆律を使用する。
規約：元成分を選び直さない。使われ方：従来実回転射の厳密回収。 -/
lemma dgModuleNaturalConeRotationHom_arrow (x : P) :
    dgModuleNaturalConeArrow R D (FS) (U) (γ) x =
      moduleConeLiftOfCycle R D (dgModuleNaturalConeArrow R D G (CF) (ν) x)
        (moduleConeRotationFirst R D (a x)) (moduleConeRotationSecond R D (a x))
        (moduleConeRotationFirst_closed R D (a x))
        (dgModuleNaturalConeRotationHom_boundary R D F G η x) := by
  let k := moduleConeLiftOfCycle R D (dgModuleNaturalConeArrow R D G (CF) (ν) x)
    (moduleConeRotationFirst R D (a x)) (moduleConeRotationSecond R D (a x))
    (moduleConeRotationFirst_closed R D (a x))
    (dgModuleNaturalConeRotationHom_boundary R D F G η x)
  change (closedHomEquiv R (RightModule R D) _ _).symm
    ((closedHomEquiv R (RightModule R D) _ _) k) = k
  exact (closedHomEquiv R (RightModule R D) _ _).symm_apply_apply _

/-- 概要：全回転比較は指定入力同型後に同じ元実回転射を回収する。
方針：同じ右包含の回収を元 cone lift に適用する。
規約：元対象と元二成分を保持。使われ方：全比較と従来の同値判定の接続。 -/
lemma dgModuleNaturalConeRotationHom_input_hom (x : P) :
    dgModuleNaturalConeArrow R D (FS) (U) (γ) x ≫
      (dgModuleNaturalConeRotationInvInputIso R D F G η x).hom =
        moduleConeRotationHom R D (a x) :=
  (congrArg (fun t => t ≫ (dgModuleNaturalConeRotationInvInputIso R D F G η x).hom)
    (dgModuleNaturalConeRotationHom_arrow R D F G η x)).trans
      (liftCongr R D _ _ (dgModuleNaturalConeInr_arrow R D F G η x) _ _
        (moduleConeRotationFirst_closed R D (a x))
        (dgModuleNaturalConeRotationHom_boundary R D F G η x)
        (moduleConeRotationInputs_cycle R D (a x)))

/-- 概要：同じ全厳密回転比較の各成分は元 K(D) の同値。
方針：元実回転射の同値性と同じ指定入力同型を使う。
規約：全自然性は前段で実証済み。使われ方：native 全関手同型の成分認証。 -/
lemma dgModuleNaturalConeRotationHom_isIso (x : P) :
    IsIso ((moduleToHomotopy R D).map
      (dgModuleNaturalConeArrow R D (FS) (U) (γ) x)) :=
  isIsoMapOfPostIso R D _ (dgModuleNaturalConeRotationInvInputIso R D F G η x)
    (moduleConeRotationHom R D (a x)) (dgModuleNaturalConeRotationHom_input_hom R D F G η x)
    (moduleConeRotationHomotopyIso R D (a x)).isIso_hom
end SerrePositivity.KST.SConstruction
