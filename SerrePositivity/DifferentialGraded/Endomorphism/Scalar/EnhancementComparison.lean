module

public import SerrePositivity.DifferentialGraded.Endomorphism.Shift
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic
public import SerrePositivity.DifferentialGraded.Module.ShiftHomotopy
public import SerrePositivity.DifferentialGraded.Endomorphism.Derived.Adjunction
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveFiniteOperations
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
public import SerrePositivity.DifferentialGraded.Category.HomotopyHomologyNaturality
public import SerrePositivity.DifferentialGraded.Functor.ModuleShift
public import SerrePositivity.DifferentialGraded.Functor.ModuleConeIso
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.PerfectStability
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionNaturality

/-!
# Endomorphism.Scalar.EnhancementComparison

## 概要
thick 閉包上の dg 像と enhancement・主 Perf の導来係数変更比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v w

/-! ## ThickHomComparison（旧 SerrePositivity/DifferentialGraded/Endomorphism/ThickHomComparison.lean） -/

/-! # 指定生成対象のthick閉包上の全Hom擬同型

K(D)内の有限なshift・三角形・retract閉包を明示し、U13のenhancementの
thick生成仮定から全Hom比較を取り出す。本質的全射は別の証明義務。
-/

@[expose] public section ThickHomComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated HomologicalComplex
open scoped ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定対象Eを含む、K(D)内の有限操作によるthick閉包。 -/
inductive endomorphismThickClosure (E : RightModule A D) :
    ObjectProperty (ModuleHomotopyCategory A D)
  | generator : endomorphismThickClosure E
      ((moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) E))
  | zero : endomorphismThickClosure E 0
  | shift {X} (s : ℤ) : endomorphismThickClosure E X → endomorphismThickClosure E (X⟦s⟧)
  | triangle (T : Triangle (ModuleHomotopyCategory A D)) (hT : T ∈ distTriang _) :
      endomorphismThickClosure E T.obj₁ → endomorphismThickClosure E T.obj₂ →
        endomorphismThickClosure E T.obj₃
  | retract {X Y} (a : Retract X Y) :
      endomorphismThickClosure E Y → endomorphismThickClosure E X

variable (E : RightModule A D)

instance endomorphismThickClosureStableUnderRetracts :
    (endomorphismThickClosure A D E).IsStableUnderRetracts where
  of_retract a h := endomorphismThickClosure.retract a h

instance endomorphismThickClosureStableUnderShift :
    (endomorphismThickClosure A D E).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨fun _ h => endomorphismThickClosure.shift s h⟩

instance endomorphismThickClosureContainsZero :
    (endomorphismThickClosure A D E).ContainsZero :=
  ⟨⟨0, Limits.isZero_zero _, endomorphismThickClosure.zero⟩⟩

instance endomorphismThickClosureTriangulatedClosed₃ :
    (endomorphismThickClosure A D E).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (fun T hT h₁ h₂ =>
    endomorphismThickClosure.triangle T hT h₁ h₂)

instance endomorphismThickClosureTriangulatedClosed₂ :
    (endomorphismThickClosure A D E).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

instance endomorphismThickClosureIsTriangulated :
    (endomorphismThickClosure A D E).IsTriangulated where

/-- 上の有限操作閉包はEを含む任意のthick部分圏に含まれる。 -/
lemma endomorphismThickClosure_le (P : ObjectProperty (ModuleHomotopyCategory A D))
    [P.IsTriangulated] [P.IsStableUnderRetracts]
    (hE : P ((moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) E))) :
    endomorphismThickClosure A D E ≤ P := by
  intro X hX
  induction hX with
  | generator => exact hE
  | zero => exact P.prop_zero
  | shift s _ ih => exact P.le_shift s _ ih
  | triangle T hT _ _ ih₁ ih₂ =>
      have h := P.ext_of_isTriangulatedClosed₃' T hT ih₁ ih₂
      simpa only [ObjectProperty.isoClosure_eq_self] using h
  | retract a _ ih => exact P.prop_of_retract a ih

lemma endomorphismHomComparison_of_thick {M : ModuleCategory A D}
    (hM : endomorphismThickClosure A D E ((moduleToHomotopy A D).obj M))
    (T : ModuleCategory A D) : QuasiIso ((endomorphismModuleHom A D E).map M T) :=
  endomorphismThickClosure_le A D E (endomorphismHomComparisonLocus A D E)
    (endomorphismHomComparisonLocus_generator A D E) _ hM T

/-- U13の全指定perfect対象がEから有限thick操作で生成される、という仮定。 -/
def endomorphismThickGeneratesPerfect (S : Set D) (E : PerfectDGModuleOver A D S) : Prop :=
  ∀ M : PerfectDGModuleOver A D S, endomorphismThickClosure A D E.val
    ((moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) M.val))

/-- thick生成の下での全Hom擬同型。H⁰の本質的全射とは独立の結論。 -/
lemma perfectEndomorphismModuleHom_homQuasiIso (S : Set D) (E : PerfectDGModuleOver A D S)
    (hgen : endomorphismThickGeneratesPerfect A D S E) :
    HomQuasiIso (perfectEndomorphismModuleHom A D S E) := by
  intro M N
  have h := endomorphismHomComparison_of_thick A D E.val (hgen M)
    (ForgetEnrichment.of (Complex A) N.val)
  change QuasiIso (𝟙 _ ≫ (endomorphismModuleHom A D E.val).map M.val N.val)
  rw [Category.id_comp]
  exact h

end SerrePositivity.DifferentialGraded
end

end ThickHomComparison

/-! ## PerfectImage（旧 SerrePositivity/DifferentialGraded/Endomorphism/PerfectImage.lean） -/

/-! # 指定対象のthick閉包のdg像はperfectに入る -/

@[expose] public section PerfectImage

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) (B : Type w)
  [DGCategory A D] [DGCategory A B] [Small.{u} D] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

def dgModuleFunctorDerivedImageComputation (M : ModuleCategory A D) :
    (F.onHomotopy ⋙ moduleHomotopyToDerivedClosed A B).obj ((moduleToHomotopy A D).obj M) ≅
      (moduleToDerived A B).obj (F.onClosed.obj M) :=
  (moduleToHomotopyDerivedIso A B).app (F.onClosed.obj M)

def dgModuleFunctorDerivedImageShiftIso (s : ℤ) (X : ModuleHomotopyCategory A D) :
    (F.onHomotopy ⋙ moduleHomotopyToDerivedClosed A B).obj (X⟦s⟧) ≅
      ((F.onHomotopy ⋙ moduleHomotopyToDerivedClosed A B).obj X)⟦s⟧ :=
  (F.onHomotopy ⋙ moduleHomotopyToDerivedClosed A B).mapIso
      (((moduleToHomotopy A D).commShiftIso s).app X.as).symm ≪≫
    dgModuleFunctorDerivedImageComputation A D B F (X.as⟦s⟧) ≪≫
    (moduleToDerived A B).mapIso
      (dgModuleFunctorShiftIso A B D F s (ForgetEnrichment.to (Complex A) X.as)) ≪≫
    ((moduleToDerived A B).commShiftIso s).app (F.onClosed.obj X.as) ≪≫
    (shiftFunctor (DerivedModuleCategory A B) s).mapIso
      (dgModuleFunctorDerivedImageComputation A D B F X.as).symm

/-- 主Kから主導来圏へ送ったdg像がperfectである、という始域上の性質。 -/
def dgModuleFunctorPerfectLocus : ObjectProperty (ModuleHomotopyCategory A D) :=
  (modulePerfect A B).inverseImage (F.onHomotopy ⋙ moduleHomotopyToDerivedClosed A B)

instance dgModuleFunctorPerfectLocusStableUnderRetracts :
    (dgModuleFunctorPerfectLocus A D B F).IsStableUnderRetracts where
  of_retract a hY := (modulePerfect A B).prop_of_retract
    (a.map (F.onHomotopy ⋙ moduleHomotopyToDerivedClosed A B)) hY

instance dgModuleFunctorPerfectLocusStableUnderShift :
    (dgModuleFunctorPerfectLocus A D B F).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨fun X hX =>
    (modulePerfect A B).prop_of_iso (dgModuleFunctorDerivedImageShiftIso A D B F s X).symm
      ((modulePerfect A B).le_shift s _ hX)⟩

lemma dgModuleFunctorPerfectLocus_triangle_obj₃
    (T : Triangle (ModuleHomotopyCategory A D)) (hT : T ∈ distTriang _)
    (h₁ : dgModuleFunctorPerfectLocus A D B F T.obj₁)
    (h₂ : dgModuleFunctorPerfectLocus A D B F T.obj₂) :
    dgModuleFunctorPerfectLocus A D B F T.obj₃ := by
  let H := F.onHomotopy ⋙ moduleHomotopyToDerivedClosed A B
  obtain ⟨M, N, f, ⟨e⟩⟩ := hT
  have hM := (modulePerfect A B).prop_of_iso
    (H.mapIso (Triangle.π₁.mapIso e) ≪≫ dgModuleFunctorDerivedImageComputation A D B F M) h₁
  have hN := (modulePerfect A B).prop_of_iso
    (H.mapIso (Triangle.π₂.mapIso e) ≪≫ dgModuleFunctorDerivedImageComputation A D B F N) h₂
  have hc := (modulePerfect A B).ext_of_isTriangulatedClosed₃'
    (moduleDerivedConeTriangle A B (F.onClosed.map f))
    (moduleDerivedConeTriangle_distinguished A B (F.onClosed.map f)) hM hN
  rw [ObjectProperty.isoClosure_eq_self] at hc
  exact (modulePerfect A B).prop_of_iso
    ((moduleToDerived A B).mapIso (dgModuleFunctorConeIso A D B F f) ≪≫
      (dgModuleFunctorDerivedImageComputation A D B F (moduleCone A D f)).symm ≪≫
      H.mapIso (Triangle.π₃.mapIso e.symm)) hc

instance dgModuleFunctorPerfectLocusTriangulatedClosed₃ :
    (dgModuleFunctorPerfectLocus A D B F).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk'
    (dgModuleFunctorPerfectLocus_triangle_obj₃ A D B F)

instance dgModuleFunctorPerfectLocusTriangulatedClosed₂ :
    (dgModuleFunctorPerfectLocus A D B F).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

lemma dgModuleFunctor_thick_perfect (E : RightModule A D)
    (hE : modulePerfect A B ((moduleToDerived A B).obj
      (F.onClosed.obj (ForgetEnrichment.of (Complex A) E))))
    {M : ModuleCategory A D}
    (hM : endomorphismThickClosure A D E ((moduleToHomotopy A D).obj M)) :
    modulePerfect A B ((moduleToDerived A B).obj (F.onClosed.obj M)) := by
  let P := dgModuleFunctorPerfectLocus A D B F
  have hEP : P ((moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) E)) :=
    (modulePerfect A B).prop_of_iso
      (dgModuleFunctorDerivedImageComputation A D B F (ForgetEnrichment.of (Complex A) E)).symm hE
  have : P.Nonempty := ObjectProperty.nonempty_of_prop hEP
  have : P.ContainsZero := inferInstance
  have : P.IsTriangulated := ⟨⟩
  exact (modulePerfect A B).prop_of_iso (dgModuleFunctorDerivedImageComputation A D B F M)
    (endomorphismThickClosure_le A D E P hEP _ hM)

variable (E : RightModule A D)

lemma endomorphismHom_thick_perfect {M : ModuleCategory A D}
    (hM : endomorphismThickClosure A D E ((moduleToHomotopy A D).obj M)) :
    modulePerfect A (EndomorphismObject E)
      ((moduleToDerived A (EndomorphismObject E)).obj
        ((endomorphismModuleHom A D E).onClosed.obj M)) := by
  apply dgModuleFunctor_thick_perfect A D (EndomorphismObject E)
    (endomorphismModuleHom A D E) E _ hM
  exact (modulePerfect A (EndomorphismObject E)).prop_of_iso
    ((moduleToDerived A (EndomorphismObject E)).mapIso (endomorphismRegularModuleIso A D E))
    (modulePerfectOver_representable A (EndomorphismObject E) .point (Set.mem_univ _))

lemma perfectEndomorphismHom_obj_perfect (S : Set D) (E : PerfectDGModuleOver A D S)
    (hgen : endomorphismThickGeneratesPerfect A D S E) (M : PerfectDGModuleOver A D S) :
    modulePerfect A (EndomorphismObject E.val)
      ((moduleToDerived A (EndomorphismObject E.val)).obj
        (ForgetEnrichment.of (Complex A) ((perfectEndomorphismModuleHom A D S E).obj M))) :=
  endomorphismHom_thick_perfect A D E.val (hgen M)

lemma perfectEndomorphismDerivedHom_obj_perfect (S : Set D) (E : PerfectDGModuleOver A D S)
    (hgen : endomorphismThickGeneratesPerfect A D S E) (X : PerfectModuleCategoryOver A D S) :
    modulePerfect A (EndomorphismObject E.val)
      ((endomorphismDerivedHom A D E.val E.property.1).obj X.obj) := by
  let R := moduleCanonicalProjectiveResolution A D X.obj.as.obj
  let e : (moduleToDerived A D).obj R.obj ≅ X.obj := moduleDerivedIso A D R.π R.quasiIso
  let M : PerfectDGModuleOver A D S :=
    ⟨ForgetEnrichment.to (Complex A) R.obj, R.projective,
      (modulePerfectOver A D S).prop_of_iso e.symm X.property⟩
  exact (modulePerfect A (EndomorphismObject E.val)).prop_of_iso
    ((endomorphismDerivedHomComputation A D E.val E.property.1 R.obj).symm ≪≫
      (endomorphismDerivedHom A D E.val E.property.1).mapIso e)
    (perfectEndomorphismHom_obj_perfect A D S E hgen M)

/-- 主導来Hom関手の、主Perfから主Perfへの実際の制限。 -/
def perfectEndomorphismHomToPerfect (S : Set D) (E : PerfectDGModuleOver A D S)
    (hgen : endomorphismThickGeneratesPerfect A D S E) :
    PerfectModuleCategoryOver A D S ⥤ PerfectModuleCategory A (EndomorphismObject E.val) :=
  (modulePerfect A (EndomorphismObject E.val)).lift
    (perfectModuleInclusion A D S ⋙ endomorphismDerivedHom A D E.val E.property.1)
    (perfectEndomorphismDerivedHom_obj_perfect A D S E hgen)

end SerrePositivity.DifferentialGraded
end

end PerfectImage

/-! ## HomotopyImage（旧 SerrePositivity/DifferentialGraded/Endomorphism/HomotopyImage.lean） -/

/-! # 加群値dg関手の主Kにおけるthick閉包の像 -/

@[expose] public section HomotopyImage

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
open scoped ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) (B : Type w)
  [DGCategory A D] [DGCategory A B] [Small.{u} D] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

def dgModuleFunctorHomotopyImageComputation (M : ModuleCategory A D) :
    F.onHomotopy.obj ((moduleToHomotopy A D).obj M) ≅
      (moduleToHomotopy A B).obj (F.onClosed.obj M) := Iso.refl _

def dgModuleFunctorHomotopyShiftIso (s : ℤ) (X : ModuleHomotopyCategory A D) :
    F.onHomotopy.obj (X⟦s⟧) ≅ (F.onHomotopy.obj X)⟦s⟧ :=
  F.onHomotopy.mapIso (((moduleToHomotopy A D).commShiftIso s).app X.as).symm ≪≫
    dgModuleFunctorHomotopyImageComputation A D B F (X.as⟦s⟧) ≪≫
    (moduleToHomotopy A B).mapIso
      (dgModuleFunctorShiftIso A B D F s (ForgetEnrichment.to (Complex A) X.as)) ≪≫
    ((moduleToHomotopy A B).commShiftIso s).app (F.onClosed.obj X.as) ≪≫
    (shiftFunctor (ModuleHomotopyCategory A B) s).mapIso
      (dgModuleFunctorHomotopyImageComputation A D B F X.as).symm

/-- dg像は指定対象の有限thick閉包を、像を含む任意のthick部分圏へ送る。 -/
lemma dgModuleFunctor_thick_image (E : RightModule A D)
    (P : ObjectProperty (ModuleHomotopyCategory A B)) [P.IsTriangulated]
    [P.IsStableUnderRetracts]
    (hE : P (F.onHomotopy.obj ((moduleToHomotopy A D).obj
      (ForgetEnrichment.of (Complex A) E)))) :
    ∀ X, endomorphismThickClosure A D E X → P (F.onHomotopy.obj X) := by
  intro X hX
  induction hX with
  | generator => exact hE
  | zero => exact P.prop_of_isZero (F.onHomotopy.map_isZero (Limits.isZero_zero _))
  | shift s _ ih =>
      exact P.prop_of_iso (dgModuleFunctorHomotopyShiftIso A D B F s _).symm
        (P.le_shift s _ ih)
  | triangle T hT _ _ ih₁ ih₂ =>
      obtain ⟨M, N, f, ⟨e⟩⟩ := hT
      have hM := P.prop_of_iso
        (F.onHomotopy.mapIso (Triangle.π₁.mapIso e) ≪≫
          dgModuleFunctorHomotopyImageComputation A D B F M) ih₁
      have hN := P.prop_of_iso
        (F.onHomotopy.mapIso (Triangle.π₂.mapIso e) ≪≫
          dgModuleFunctorHomotopyImageComputation A D B F N) ih₂
      have hc := P.ext_of_isTriangulatedClosed₃'
        (moduleHomotopyConeTriangle A B (F.onClosed.map f))
        (moduleHomotopyConeTriangle_distinguished A B (F.onClosed.map f)) hM hN
      rw [ObjectProperty.isoClosure_eq_self] at hc
      exact P.prop_of_iso
        ((moduleToHomotopy A B).mapIso (dgModuleFunctorConeIso A D B F f) ≪≫
          (dgModuleFunctorHomotopyImageComputation A D B F (moduleCone A D f)).symm ≪≫
          F.onHomotopy.mapIso (Triangle.π₃.mapIso e.symm)) hc
  | retract a _ ih => exact P.prop_of_retract (a.map F.onHomotopy) ih

end SerrePositivity.DifferentialGraded
end

end HomotopyImage

/-! ## HomotopyShiftCoherence（旧 SerrePositivity/DifferentialGraded/Endomorphism/HomotopyShiftCoherence.lean） -/

/-! # 正規化shift比較を主ホモトピー圏へ降ろす -/

@[expose] public section HomotopyShiftCoherence

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (B : Type w) [DGCategory A B] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

/-- 全Hom写像から得た整合的shift比較を境界商へ降ろす。 -/
@[instance_reducible]
def dgModuleFunctorHomotopyCommShift : F.onHomotopy.CommShift ℤ := by
  letI := dgModuleFunctorCommShift A D B F
  unfold DGFunctor.onHomotopy
  infer_instance

/-- 閉零加群から主Kへの因子分解の自然同型。 -/
def dgModuleFunctorHomotopyFacIso :
    moduleToHomotopy A D ⋙ F.onHomotopy ≅ F.onClosed ⋙ moduleToHomotopy A B :=
  Quotient.lift.isLift _ _ _

section
local instance : F.onClosed.CommShift ℤ := dgModuleFunctorCommShift A D B F
local instance : F.onHomotopy.CommShift ℤ := dgModuleFunctorHomotopyCommShift A D B F

lemma dgModuleFunctorHomotopyFacIso_commShift :
    NatTrans.CommShift (dgModuleFunctorHomotopyFacIso A D B F).hom ℤ := by
  unfold dgModuleFunctorHomotopyFacIso
  exact Quotient.liftCommShift_compatibility _ _ _ _

end
end SerrePositivity.DifferentialGraded
end

end HomotopyShiftCoherence

/-! ## ProjectiveImage（旧 SerrePositivity/DifferentialGraded/Endomorphism/ProjectiveImage.lean） -/

/-! # 指定対象のthick閉包のHom像のホモトピー射影性 -/

@[expose] public section ProjectiveImage

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleHomotopyProjectiveLocus : ObjectProperty (ModuleHomotopyCategory A D) :=
  fun X => moduleHomotopicallyProjective A D X.as

instance moduleHomotopyProjectiveLocusStableUnderRetracts :
    (moduleHomotopyProjectiveLocus A D).IsStableUnderRetracts where
  of_retract {X Y} a hY := by
    obtain ⟨i, hi⟩ := (moduleToHomotopy A D).map_surjective a.i
    obtain ⟨r, hr⟩ := (moduleToHomotopy A D).map_surjective a.r
    apply moduleHomotopicallyProjective_of_homotopyRetract A D i r _ hY
    rw [CategoryTheory.Functor.map_comp, hi, hr, a.retract]
    exact ((moduleToHomotopy A D).map_id X.as).symm

instance moduleHomotopyProjectiveLocusStableUnderShift :
    (moduleHomotopyProjectiveLocus A D).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨fun X hX =>
    (moduleHomotopyProjectiveLocus A D).prop_of_iso
      (((moduleToHomotopy A D).commShiftIso s).app X.as)
      (moduleHomotopicallyProjective_shift A D hX s)⟩

lemma moduleHomotopyProjectiveLocus_triangle_obj₃
    (T : Triangle (ModuleHomotopyCategory A D)) (hT : T ∈ distTriang _)
    (h₁ : moduleHomotopyProjectiveLocus A D T.obj₁)
    (h₂ : moduleHomotopyProjectiveLocus A D T.obj₂) :
    moduleHomotopyProjectiveLocus A D T.obj₃ := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := hT
  have hM := (moduleHomotopyProjectiveLocus A D).prop_of_iso (Triangle.π₁.mapIso e) h₁
  have hN := (moduleHomotopyProjectiveLocus A D).prop_of_iso (Triangle.π₂.mapIso e) h₂
  exact (moduleHomotopyProjectiveLocus A D).prop_of_iso (Triangle.π₃.mapIso e.symm)
    (moduleHomotopicallyProjective_cone A D hM hN f)

instance moduleHomotopyProjectiveLocusTriangulatedClosed₃ :
    (moduleHomotopyProjectiveLocus A D).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (moduleHomotopyProjectiveLocus_triangle_obj₃ A D)

instance moduleHomotopyProjectiveLocusTriangulatedClosed₂ :
    (moduleHomotopyProjectiveLocus A D).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

instance moduleHomotopyProjectiveLocusNonempty :
    (moduleHomotopyProjectiveLocus A D).Nonempty :=
  ObjectProperty.nonempty_of_prop (X := (moduleToHomotopy A D).obj (moduleZero A D))
    (moduleHomotopicallyProjective_of_isZero A D (moduleZero_isZero A D))

instance moduleHomotopyProjectiveLocusContainsZero :
    (moduleHomotopyProjectiveLocus A D).ContainsZero := inferInstance

instance moduleHomotopyProjectiveLocusIsTriangulated :
    (moduleHomotopyProjectiveLocus A D).IsTriangulated where

variable (E : RightModule A D)

lemma endomorphismHom_thick_projective {M : ModuleCategory A D}
    (hM : endomorphismThickClosure A D E ((moduleToHomotopy A D).obj M)) :
    moduleHomotopicallyProjective A (EndomorphismObject E)
      ((endomorphismModuleHom A D E).onClosed.obj M) := by
  have hE : moduleHomotopyProjectiveLocus A (EndomorphismObject E)
      ((endomorphismModuleHom A D E).onHomotopy.obj
        ((moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) E))) :=
    moduleHomotopicallyProjective_of_iso A (EndomorphismObject E)
      (endomorphismRegularModuleIso A D E)
      (representable_homotopicallyProjective A (EndomorphismObject E) .point)
  exact dgModuleFunctor_thick_image A D (EndomorphismObject E) (endomorphismModuleHom A D E)
    E (moduleHomotopyProjectiveLocus A (EndomorphismObject E)) hE _ hM

lemma perfectEndomorphismHom_obj_projective (S : Set D) (E : PerfectDGModuleOver A D S)
    (hgen : endomorphismThickGeneratesPerfect A D S E) (M : PerfectDGModuleOver A D S) :
    moduleHomotopicallyProjective A (EndomorphismObject E.val)
      (ForgetEnrichment.of (Complex A) ((perfectEndomorphismModuleHom A D S E).obj M)) :=
  endomorphismHom_thick_projective A D E.val (hgen M)

end SerrePositivity.DifferentialGraded
end

end ProjectiveImage

/-! ## ProjectiveHomotopyComparison（旧 SerrePositivity/DifferentialGraded/Endomorphism/ProjectiveHomotopyComparison.lean） -/

/-! # 射影的主K部分圏を介したU13のambient包含のshift整合性 -/

@[expose] public section ProjectiveHomotopyComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

abbrev projectiveModuleHomotopyCategory := (moduleHomotopyProjectiveLocus A D).FullSubcategory

def projectiveModuleHomotopyToDerived :
    projectiveModuleHomotopyCategory A D ⥤ DerivedModuleCategory A D :=
  (moduleHomotopyProjectiveLocus A D).ι ⋙ moduleHomotopyToDerivedClosed A D

instance projectiveModuleHomotopyToDerivedFull :
    (projectiveModuleHomotopyToDerived A D).Full where
  map_surjective {X Y} f := by
    obtain ⟨g, hg⟩ := (moduleProjectiveLocalization_map_bijective A D X.property Y.obj).2 f
    exact ⟨ObjectProperty.homMk g, hg⟩

instance projectiveModuleHomotopyToDerivedFaithful :
    (projectiveModuleHomotopyToDerived A D).Faithful where
  map_injective {X Y} _f _g h :=
    (moduleHomotopyProjectiveLocus A D).hom_ext
      ((moduleProjectiveLocalization_map_bijective A D X.property Y.obj).1 h)

instance projectiveModuleHomotopyToDerivedCommShift :
    (projectiveModuleHomotopyToDerived A D).CommShift ℤ := by
  unfold projectiveModuleHomotopyToDerived
  infer_instance

instance projectiveModuleHomotopyToDerivedIsTriangulated :
    (projectiveModuleHomotopyToDerived A D).IsTriangulated := by
  unfold projectiveModuleHomotopyToDerived
  infer_instance

def perfectDGModuleInclusionProjectiveHomotopy (S : Set D) :
    PerfectDGHomotopyCategoryOver A D S ⥤ projectiveModuleHomotopyCategory A D :=
  (moduleHomotopyProjectiveLocus A D).lift (perfectDGModuleInclusion A D S).onHomotopy
    (fun X => (ForgetEnrichment.to (Complex A) X.as).property.1)

def perfectDGModuleInclusionProjectiveHomotopyIso (S : Set D) :
    perfectDGModuleInclusionProjectiveHomotopy A D S ⋙
        (moduleHomotopyProjectiveLocus A D).ι ≅
      (perfectDGModuleInclusion A D S).onHomotopy :=
  (moduleHomotopyProjectiveLocus A D).liftCompιIso _
    (fun X => (ForgetEnrichment.to (Complex A) X.as).property.1)

def perfectDGModuleInclusionProjectiveHomotopyDerivedIso (S : Set D) :
    perfectDGModuleInclusionProjectiveHomotopy A D S ⋙ projectiveModuleHomotopyToDerived A D ≅
      perfectDGModuleToDerived A D S :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectDGModuleInclusionProjectiveHomotopyIso A D S)
      (moduleHomotopyToDerivedClosed A D)

@[instance_reducible]
def perfectDGModuleInclusionProjectiveHomotopyCommShift (S : Set D) :
    (perfectDGModuleInclusionProjectiveHomotopy A D S).CommShift ℤ :=
  Functor.CommShift.ofComp (perfectDGModuleInclusionProjectiveHomotopyDerivedIso A D S) ℤ

lemma perfectDGModuleInclusionProjectiveHomotopyIsTriangulated (S : Set D) :
    letI := perfectDGModuleInclusionProjectiveHomotopyCommShift A D S
    (perfectDGModuleInclusionProjectiveHomotopy A D S).IsTriangulated := by
  let := perfectDGModuleInclusionProjectiveHomotopyCommShift A D S
  let := Functor.CommShift.ofComp_compatibility
    (perfectDGModuleInclusionProjectiveHomotopyDerivedIso A D S) ℤ
  exact (Functor.isTriangulated_iff_comp_right
    (perfectDGModuleInclusionProjectiveHomotopyDerivedIso A D S)).2 inferInstance

@[instance_reducible]
def perfectDGModuleInclusionHomotopyCommShift (S : Set D) :
    (perfectDGModuleInclusion A D S).onHomotopy.CommShift ℤ := by
  letI := perfectDGModuleInclusionProjectiveHomotopyCommShift A D S
  exact Functor.CommShift.ofIso (perfectDGModuleInclusionProjectiveHomotopyIso A D S) ℤ

lemma perfectDGModuleInclusionHomotopyIsTriangulated (S : Set D) :
    letI := perfectDGModuleInclusionHomotopyCommShift A D S
    (perfectDGModuleInclusion A D S).onHomotopy.IsTriangulated := by
  let := perfectDGModuleInclusionProjectiveHomotopyCommShift A D S
  let := perfectDGModuleInclusionHomotopyCommShift A D S
  let := perfectDGModuleInclusionProjectiveHomotopyIsTriangulated A D S
  let := Functor.CommShift.ofIso_compatibility
    (perfectDGModuleInclusionProjectiveHomotopyIso A D S) ℤ
  have : (perfectDGModuleInclusionProjectiveHomotopy A D S ⋙
      (moduleHomotopyProjectiveLocus A D).ι).IsTriangulated := inferInstance
  exact Functor.isTriangulated_of_iso (perfectDGModuleInclusionProjectiveHomotopyIso A D S)

end SerrePositivity.DifferentialGraded
end

end ProjectiveHomotopyComparison

/-! ## QuasiFullyFaithful（旧 SerrePositivity/DifferentialGraded/Endomorphism/QuasiFullyFaithful.lean） -/

/-! # 全Hom擬同型から主H⁰の完全忠実性への比較

全Hom写像の次数零Homologyを用い、H⁰の射計算と自然に照合する。
-/

@[expose] public section QuasiFullyFaithful

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A] {C : Type v} {B : Type w}
  [DGCategory A C] [DGCategory A B] (F : DGFunctor A C B)

lemma dgHomMap_closedCycle {x y : ClosedCategory A C} (f : x ⟶ y) :
    complexMapZeroCycle A (F.map x y) (closedHomEquiv A C x y f) =
      closedHomEquiv A B (F.onClosed.obj x) (F.onClosed.obj y) (F.onClosed.map f) := by
  apply Subtype.ext
  exact (cycleFromUnit_postcomp (ForgetEnrichment.homTo (Complex A) f) (F.map x y)).symm

lemma dgHomMap_homotopyHomologyEquiv (x y : ClosedCategory A C)
    (f : (toHomotopy A C).obj x ⟶ (toHomotopy A C).obj y) :
    homotopyHomologyEquiv A B (F.onClosed.obj x) (F.onClosed.obj y) (F.onHomotopy.map f) =
      homologyMap (F.map x y) 0 (homotopyHomologyEquiv A C x y f) := by
  obtain ⟨f, rfl⟩ := (toHomotopy A C).map_surjective f
  change homotopyHomologyEquiv A B (F.onClosed.obj x) (F.onClosed.obj y)
      ((toHomotopy A B).map (F.onClosed.map f)) = _
  rw [homotopyHomologyEquiv_map, homotopyHomologyEquiv_map,
    complexZeroHomologyClass_naturality, dgHomMap_closedCycle]
  rfl

lemma dgHomMap_onHomotopy_bijective (hF : HomQuasiIso F) (X Y : HomotopyCategory A C) :
    Function.Bijective (F.onHomotopy.map (X := X) (Y := Y)) := by
  obtain ⟨x⟩ := X
  obtain ⟨y⟩ := Y
  have := hF x y
  have hb := (ConcreteCategory.isIso_iff_bijective (homologyMap (F.map x y) 0)).mp inferInstance
  let eC := homotopyHomologyEquiv A C x y
  let eB := homotopyHomologyEquiv A B (F.onClosed.obj x) (F.onClosed.obj y)
  constructor
  · intro f g h
    apply eC.injective
    apply hb.1
    exact (dgHomMap_homotopyHomologyEquiv F x y f).symm.trans
      ((congrArg eB h).trans (dgHomMap_homotopyHomologyEquiv F x y g))
  · intro f
    obtain ⟨c, hc⟩ := hb.2 (eB f)
    refine ⟨eC.symm c, eB.injective ?_⟩
    exact (dgHomMap_homotopyHomologyEquiv F x y (eC.symm c)).trans
      ((congrArg (homologyMap (F.map x y) 0) (eC.apply_symm_apply c)).trans hc)

lemma dgHomMap_onHomotopy_full (hF : HomQuasiIso F) : F.onHomotopy.Full where
  map_surjective {X Y} := (dgHomMap_onHomotopy_bijective F hF X Y).2

lemma dgHomMap_onHomotopy_faithful (hF : HomQuasiIso F) : F.onHomotopy.Faithful where
  map_injective {X Y} := (dgHomMap_onHomotopy_bijective F hF X Y).1

variable (A) (D : Type v) [DGCategory A D] [Small.{u} D]

lemma perfectEndomorphismModuleHom_onHomotopy_full (S : Set D)
    (E : PerfectDGModuleOver A D S) (hgen : endomorphismThickGeneratesPerfect A D S E) :
    (perfectEndomorphismModuleHom A D S E).onHomotopy.Full :=
  dgHomMap_onHomotopy_full _ (perfectEndomorphismModuleHom_homQuasiIso A D S E hgen)

lemma perfectEndomorphismModuleHom_onHomotopy_faithful (S : Set D)
    (E : PerfectDGModuleOver A D S) (hgen : endomorphismThickGeneratesPerfect A D S E) :
    (perfectEndomorphismModuleHom A D S E).onHomotopy.Faithful :=
  dgHomMap_onHomotopy_faithful _ (perfectEndomorphismModuleHom_homQuasiIso A D S E hgen)

end SerrePositivity.DifferentialGraded
end

end QuasiFullyFaithful

/-! ## ShiftConeComparison（旧 SerrePositivity/DifferentialGraded/Endomorphism/ShiftConeComparison.lean） -/

/-! # 再構成Hom・tensorの評価成分のshift・cone図式

全次数dg写像でshiftの斉次単位とconeの包含を送る標準比較を使用する。
ここでは評価後の複体図式を与え、Perf上の三角同値は別の証明義務として残す。
-/

@[expose] public section ShiftConeComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- Hom(E,−)の正則End対象での評価。 -/
def endomorphismHomComponent : DGFunctor A (RightModule A D) (Complex A) :=
  (endomorphismModuleHom A D E).comp (moduleEvaluationDG A (EndomorphismObject E) .point)

lemma endomorphismHomComponent_obj (M : RightModule A D) :
    (endomorphismHomComponent A D E).obj M = moduleHom A D E M := rfl

lemma endomorphismHomComponent_eq :
    endomorphismHomComponent A D E = leftRepresentable A E := by
  apply EnrichedFunctor.ext (Complex A)
    (F := endomorphismHomComponent A D E) (G := leftRepresentable A E) (fun _ => rfl)
  intro M N
  simp only [eqToHom_refl, Category.comp_id]
  exact endomorphismModuleHom_map_π A D E M N

/-- 指定対象EとのtensorをDの対象dで評価する。 -/
def endomorphismTensorComponent (d : D) :
    DGFunctor A (RightModule A (EndomorphismObject E)) (Complex A) :=
  (endomorphismModuleTensor A D E).comp (moduleEvaluationDG A D d)

lemma endomorphismTensorComponent_obj (d : D) (N : RightModule A (EndomorphismObject E)) :
    (endomorphismTensorComponent A D E d).obj N =
      BalancedTensor.obj A (EndomorphismObject E) N ((endomorphismModuleAction A D E).leftAt d) :=
  rfl

lemma endomorphismTensorComponent_eq (d : D) :
    endomorphismTensorComponent A D E d =
      BalancedTensor.rightTensorDG A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := endomorphismTensorComponent A D E d)
    (G := BalancedTensor.rightTensorDG A (EndomorphismObject E)
      ((endomorphismModuleAction A D E).leftAt d)) (fun _ => rfl)
  intro M N
  simp only [eqToHom_refl, Category.comp_id]
  exact endomorphismModuleTensor_map_π A D E M N d

/-- 全Homのshift比較。Eの射影性やflat性は不要。 -/
def endomorphismHomShiftIso (s : ℤ) (M : RightModule A D) :
    moduleHom A D E (shiftModule s M) ≅ (moduleHom A D E M)⟦s⟧ :=
  DGFunctor.moduleShiftImageIso A D (endomorphismHomComponent A D E) s M

/-- 再構成tensorの各D成分でのshift比較。 -/
def endomorphismTensorShiftIso (d : D) (s : ℤ)
    (N : RightModule A (EndomorphismObject E)) :
    (endomorphismTensorComponent A D E d).obj (shiftModule s N) ≅
      ((endomorphismTensorComponent A D E d).obj N)⟦s⟧ :=
  DGFunctor.moduleShiftImageIso A (EndomorphismObject E)
    (endomorphismTensorComponent A D E d) s N

lemma endomorphismTensorShiftIso_eq (d : D) (s : ℤ)
    (N : RightModule A (EndomorphismObject E)) :
    endomorphismTensorShiftIso A D E d s N =
      BalancedTensor.rightTensorShiftIso A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) s N := by
  apply Iso.ext
  apply HomologicalComplex.hom_ext
  intro i
  change (DGFunctor.moduleShiftImageComparison A (EndomorphismObject E)
      (endomorphismTensorComponent A D E d) s N).f i =
    (DGFunctor.moduleShiftImageComparison A (EndomorphismObject E)
      (BalancedTensor.rightTensorDG A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d)) s N).f i
  rw [DGFunctor.moduleShiftImageComparison_f, DGFunctor.moduleShiftImageComparison_f]
  exact congrArg (fun k => (k.f s (moduleShiftOutElement A (EndomorphismObject E) s N)).v
    i (i + s) rfl) (endomorphismModuleTensor_map_π A D E (shiftModule s N) N d)

/-- Hom(E,−)の標準coneに対する実際の複体同型。 -/
def endomorphismHomConeIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone (((endomorphismHomComponent A D E).toComplexFunctor A).map f) ≅
      ((endomorphismHomComponent A D E).toComplexFunctor A).obj (moduleCone A D f) :=
  DGFunctor.moduleConeImageIso A D (endomorphismHomComponent A D E) f

/-- tensorの標準coneに対する各D成分の複体同型。 -/
def endomorphismTensorConeIso (d : D)
    {M N : ModuleCategory A (EndomorphismObject E)} (f : M ⟶ N) :
    mappingCone (((endomorphismTensorComponent A D E d).toComplexFunctor A).map f) ≅
      ((endomorphismTensorComponent A D E d).toComplexFunctor A).obj
        (moduleCone A (EndomorphismObject E) f) :=
  DGFunctor.moduleConeImageIso A (EndomorphismObject E) (endomorphismTensorComponent A D E d) f

lemma endomorphismHomConeIso_inr {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone.inr (((endomorphismHomComponent A D E).toComplexFunctor A).map f) ≫
        (endomorphismHomConeIso A D E f).hom =
      ((endomorphismHomComponent A D E).toComplexFunctor A).map (moduleConeInr A D f) :=
  DGFunctor.moduleConeImageComparison_inr A D (endomorphismHomComponent A D E) f

lemma endomorphismHomConeIso_inl {M N : ModuleCategory A D} (f : M ⟶ N) :
    (mappingCone.inl (((endomorphismHomComponent A D E).toComplexFunctor A).map f)).comp
        (Cochain.ofHom (endomorphismHomConeIso A D E f).hom) (add_zero (-1)) =
      DGFunctor.moduleConeImageInl A D (endomorphismHomComponent A D E) f :=
  DGFunctor.moduleConeImageComparison_inl A D (endomorphismHomComponent A D E) f

lemma endomorphismTensorConeIso_inr (d : D)
    {M N : ModuleCategory A (EndomorphismObject E)} (f : M ⟶ N) :
    mappingCone.inr (((endomorphismTensorComponent A D E d).toComplexFunctor A).map f) ≫
        (endomorphismTensorConeIso A D E d f).hom =
      ((endomorphismTensorComponent A D E d).toComplexFunctor A).map
        (moduleConeInr A (EndomorphismObject E) f) :=
  DGFunctor.moduleConeImageComparison_inr A (EndomorphismObject E)
    (endomorphismTensorComponent A D E d) f

lemma endomorphismTensorConeIso_inl (d : D)
    {M N : ModuleCategory A (EndomorphismObject E)} (f : M ⟶ N) :
    (mappingCone.inl (((endomorphismTensorComponent A D E d).toComplexFunctor A).map f)).comp
        (Cochain.ofHom (endomorphismTensorConeIso A D E d f).hom) (add_zero (-1)) =
      DGFunctor.moduleConeImageInl A (EndomorphismObject E)
        (endomorphismTensorComponent A D E d) f :=
  DGFunctor.moduleConeImageComparison_inl A (EndomorphismObject E)
    (endomorphismTensorComponent A D E d) f

end SerrePositivity.DifferentialGraded
end

end ShiftConeComparison

/-! ## PerfectDGComparison（旧 SerrePositivity/DifferentialGraded/Endomorphism/PerfectDGComparison.lean） -/

/-! # U13のperfect dg enhancement間の実際の再構成Hom比較 -/

@[expose] public section PerfectDGComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)

/-- Hom像の射影性・perfect性の証拠を保持した、実際のdg enhancement間の関手。 -/
def perfectEndomorphismDG :
    DGFunctor A (PerfectDGModuleOver A D S) (PerfectDGModule A (EndomorphismObject E.val)) where
  obj M := ⟨(perfectEndomorphismModuleHom A D S E).obj M,
    perfectEndomorphismHom_obj_projective A D S E hgen M,
    perfectEndomorphismHom_obj_perfect A D S E hgen M⟩
  map M N := (perfectEndomorphismModuleHom A D S E).map M N
  map_id M := (perfectEndomorphismModuleHom A D S E).map_id M
  map_comp M N P := (perfectEndomorphismModuleHom A D S E).map_comp M N P

/-- enhancement間の各Hom写像の擬同型。本質的全射とは分けて保持する。 -/
lemma perfectEndomorphismDG_homQuasiIso : HomQuasiIso (perfectEndomorphismDG A D S E hgen) :=
  perfectEndomorphismModuleHom_homQuasiIso A D S E hgen

instance perfectEndomorphismDGHomotopyFull :
    (perfectEndomorphismDG A D S E hgen).onHomotopy.Full :=
  dgHomMap_onHomotopy_full _ (perfectEndomorphismDG_homQuasiIso A D S E hgen)

instance perfectEndomorphismDGHomotopyFaithful :
    (perfectEndomorphismDG A D S E hgen).onHomotopy.Faithful :=
  dgHomMap_onHomotopy_faithful _ (perfectEndomorphismDG_homQuasiIso A D S E hgen)

/-- 実際の加群への包含は、元のHom関手とdgレベルで可換。 -/
lemma perfectEndomorphismDG_inclusion_square :
    (perfectEndomorphismDG A D S E hgen).comp
        (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ) =
      perfectEndomorphismModuleHom A D S E := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (perfectEndomorphismDG A D S E hgen).comp
      (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ))
    (G := perfectEndomorphismModuleHom A D S E) (fun _ => rfl)
  intro M N
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end SerrePositivity.DifferentialGraded
end

end PerfectDGComparison

/-! ## ScalarPerfectEnhancement（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarPerfectEnhancement.lean） -/

/-! # 実際の係数拡大のU13 enhancementへの制限 -/

@[expose] public section ScalarPerfectEnhancement

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 係数変更したU13 enhancementから、実際の係数変更加群のenhancementへの比較。 -/
def scalarPerfectDG (S : Set D) :
    DGFunctor A' (ScalarExtension.DGBaseChange φ (PerfectDGModuleOver A D S))
      (PerfectDGModuleOver A' (ScalarExtension.DGBaseChange φ D)
        (scalarPerfectGenerators φ D S)) where
  obj M := ⟨ScalarExtension.rightModule φ D M.val,
    scalarModuleExtension_projective_perfect φ D M.property.1 M.property.2,
    scalarModuleExtension_perfect_perfect φ D M.property.1 M.property.2⟩
  map M N := scalarModuleHom φ D M.val N.val
  map_id M := scalarModuleHom_identity φ D M.val
  map_comp M N P := scalarModuleHom_composition φ D M.val N.val P.val

lemma scalarPerfectDG_homQuasiIso (S : Set D) : HomQuasiIso (scalarPerfectDG φ D S) := by
  intro M N
  exact scalarModuleHom_quasiIso_of_perfect φ D M.property.1 M.property.2
    (ForgetEnrichment.of (Complex A) N.val)

instance scalarPerfectDGHomotopyFull (S : Set D) :
    (scalarPerfectDG φ D S).onHomotopy.Full :=
  dgHomMap_onHomotopy_full _ (scalarPerfectDG_homQuasiIso φ D S)

instance scalarPerfectDGHomotopyFaithful (S : Set D) :
    (scalarPerfectDG φ D S).onHomotopy.Faithful :=
  dgHomMap_onHomotopy_faithful _ (scalarPerfectDG_homQuasiIso φ D S)

lemma scalarPerfectDG_inclusion_square (S : Set D) :
    (scalarPerfectDG φ D S).comp
        (perfectDGModuleInclusion A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S)) =
      (ScalarExtension.dgFunctor φ (perfectDGModuleInclusion A D S)).comp
        (scalarModuleDGFunctor φ D) := by
  apply EnrichedFunctor.ext (Complex A')
    (F := (scalarPerfectDG φ D S).comp
      (perfectDGModuleInclusion A' (ScalarExtension.DGBaseChange φ D)
        (scalarPerfectGenerators φ D S)))
    (G := (ScalarExtension.dgFunctor φ (perfectDGModuleInclusion A D S)).comp
      (scalarModuleDGFunctor φ D)) (fun _ => rfl)
  intro M N
  change scalarModuleHom φ D M.val N.val ≫ 𝟙 _ =
    (ScalarExtension.extension φ).map (𝟙 _) ≫ scalarModuleHom φ D M.val N.val
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end SerrePositivity.DifferentialGraded
end

end ScalarPerfectEnhancement

/-! ## ScalarDerivedProjectiveComparison（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarDerivedProjectiveComparison.lean） -/

/-! # 射影的加群での既存導来係数拡大と実際の係数拡大の一致 -/

@[expose] public section ScalarDerivedProjectiveComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarDerivedExtensionAugmentation_isIso_of_projective (M : ModuleCategory A D)
    (hM : moduleHomotopicallyProjective A D M) :
    IsIso ((ScalarExtension.derivedExtensionAugmentation φ D).app M) := by
  let P := moduleCanonicalProjectiveResolution A D M
  have : IsIso ((moduleToHomotopy A D).map P.π) :=
    moduleHomotopicallyProjective_quasiIso_isIso_homotopy A D P.projective hM P.π P.quasiIso
  have : IsIso ((moduleToDerived A' (ScalarExtension.DGBaseChange φ D)).map
      ((ScalarExtension.moduleExtension φ D).map P.π)) := by
    change IsIso ((ScalarExtension.moduleExtensionHomotopyToDerived φ D).map
      ((moduleToHomotopy A D).map P.π))
    infer_instance
  rw [ScalarExtension.derivedExtensionAugmentation_app]
  infer_instance

def scalarDerivedProjectiveComputation (M : ModuleCategory A D)
    (hM : moduleHomotopicallyProjective A D M) :
    (ScalarExtension.derivedExtension φ D).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A' (ScalarExtension.DGBaseChange φ D)).obj
        ((ScalarExtension.moduleExtension φ D).obj M) := by
  have := scalarDerivedExtensionAugmentation_isIso_of_projective φ D M hM
  exact asIso ((ScalarExtension.derivedExtensionAugmentation φ D).app M)

lemma scalarDerivedProjectiveComputation_naturality {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) :
    (ScalarExtension.derivedExtension φ D).map ((moduleToDerived A D).map f) ≫
        (scalarDerivedProjectiveComputation φ D N hN).hom =
      (scalarDerivedProjectiveComputation φ D M hM).hom ≫
        (moduleToDerived A' (ScalarExtension.DGBaseChange φ D)).map
          ((ScalarExtension.moduleExtension φ D).map f) :=
  (ScalarExtension.derivedExtensionAugmentation φ D).naturality f

end SerrePositivity.DifferentialGraded
end

end ScalarDerivedProjectiveComparison

/-! ## ScalarDerivedPerfect（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarDerivedPerfect.lean） -/

/-! # 既存の導来係数拡大の主Perfへの制限 -/

@[expose] public section ScalarDerivedPerfect

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarDerivedExtension_obj_perfect (S : Set D) (X : PerfectModuleCategoryOver A D S) :
    modulePerfectOver A' (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S)
      ((ScalarExtension.derivedExtension φ D).obj X.obj) := by
  let R := moduleCanonicalProjectiveResolution A D X.obj.as.obj
  let e : (moduleToDerived A D).obj R.obj ≅ X.obj := moduleDerivedIso A D R.π R.quasiIso
  have hR := (modulePerfectOver A D S).prop_of_iso e.symm X.property
  exact (modulePerfectOver A' (ScalarExtension.DGBaseChange φ D)
    (scalarPerfectGenerators φ D S)).prop_of_iso
      ((scalarDerivedProjectiveComputation φ D R.obj R.projective).symm ≪≫
        (ScalarExtension.derivedExtension φ D).mapIso e)
      (scalarModuleExtension_perfect_perfect φ D R.projective hR)

/-- 受入済みの主導来係数拡大を、指定集合から生成する主Perfへ制限する。 -/
def perfectScalarDerivedExtension (S : Set D) :
    PerfectModuleCategoryOver A D S ⥤
      PerfectModuleCategoryOver A' (ScalarExtension.DGBaseChange φ D)
        (scalarPerfectGenerators φ D S) :=
  (modulePerfectOver A' (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S)).lift
    (perfectModuleInclusion A D S ⋙ ScalarExtension.derivedExtension φ D)
    (scalarDerivedExtension_obj_perfect φ D S)

def perfectScalarDerivedExtensionInclusionIso (S : Set D) :
    perfectScalarDerivedExtension φ D S ⋙
        perfectModuleInclusion A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S) ≅
      perfectModuleInclusion A D S ⋙ ScalarExtension.derivedExtension φ D :=
  ObjectProperty.liftCompιIso _ _ _

end SerrePositivity.DifferentialGraded
end

end ScalarDerivedPerfect

/-! ## ScalarEnhancementClosed（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarEnhancementClosed.lean） -/

/-! # 元と係数変更後のenhancementの閉零圏・H⁰を結ぶ実際の関手 -/

@[expose] public section ScalarEnhancementClosed

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 係数環の異なる二つのenhancementの閉零圏間の、実際の加群係数拡大。 -/
def scalarPerfectClosedExtension (S : Set D) :
    ClosedCategory A (PerfectDGModuleOver A D S) ⥤
      ClosedCategory A' (PerfectDGModuleOver A' (ScalarExtension.DGBaseChange φ D)
        (scalarPerfectGenerators φ D S)) where
  obj M := by
    let M' : PerfectDGModuleOver A D S := ForgetEnrichment.to (Complex A) M
    exact ForgetEnrichment.of (Complex A')
      (⟨ScalarExtension.rightModule φ D M'.val,
        scalarModuleExtension_projective_perfect φ D M'.property.1 M'.property.2,
        scalarModuleExtension_perfect_perfect φ D M'.property.1 M'.property.2⟩ :
        PerfectDGModuleOver A' (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S))
  map {M N} f := by
    let M' : PerfectDGModuleOver A D S := ForgetEnrichment.to (Complex A) M
    let N' : PerfectDGModuleOver A D S := ForgetEnrichment.to (Complex A) N
    change 𝟙_ (Complex A') ⟶ moduleHom A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D M'.val) (ScalarExtension.rightModule φ D N'.val)
    let f' : ForgetEnrichment.of (Complex A) M'.val ⟶
        ForgetEnrichment.of (Complex A) N'.val :=
      (perfectDGModuleInclusion A D S).onClosed.map f
    exact ForgetEnrichment.homTo (Complex A') ((ScalarExtension.moduleExtension φ D).map f')
  map_id M := by
    change (ScalarExtension.moduleExtension φ D).map
      ((perfectDGModuleInclusion A D S).onClosed.map (𝟙 M)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    change (ScalarExtension.moduleExtension φ D).map
      ((perfectDGModuleInclusion A D S).onClosed.map (f ≫ g)) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rfl

def scalarPerfectClosedInclusionIso (S : Set D) :
    scalarPerfectClosedExtension φ D S ⋙
        (perfectDGModuleInclusion A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S)).onClosed ≅
      (perfectDGModuleInclusion A D S).onClosed ⋙ ScalarExtension.moduleExtension φ D :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]
    rfl)

def scalarPerfectHomotopyExtension (S : Set D) :
    PerfectDGHomotopyCategoryOver A D S ⥤
      PerfectDGHomotopyCategoryOver A' (ScalarExtension.DGBaseChange φ D)
        (scalarPerfectGenerators φ D S) :=
  CategoryTheory.Quotient.lift _ (scalarPerfectClosedExtension φ D S ⋙
    toHomotopy A' (PerfectDGModuleOver A' (ScalarExtension.DGBaseChange φ D)
      (scalarPerfectGenerators φ D S))) (by
      intro M N f g hb
      apply (perfectDGModuleInclusion A' (ScalarExtension.DGBaseChange φ D)
        (scalarPerfectGenerators φ D S)).onHomotopy.map_injective
      have h := (perfectDGModuleInclusion A D S).preserves_boundary f g hb
      obtain ⟨hh⟩ := (moduleHomotopy_nonempty_iff A D _ _).2 h
      change (moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D)).map
          ((ScalarExtension.moduleExtension φ D).map
            ((perfectDGModuleInclusion A D S).onClosed.map f)) =
        (moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D)).map
          ((ScalarExtension.moduleExtension φ D).map
            ((perfectDGModuleInclusion A D S).onClosed.map g))
      exact (moduleToHomotopy_map_eq_iff A' (ScalarExtension.DGBaseChange φ D) _ _).2
        ⟨scalarModuleHomotopy φ D hh⟩)

lemma scalarPerfectHomotopyExtension_fac (S : Set D) :
    toHomotopy A (PerfectDGModuleOver A D S) ⋙ scalarPerfectHomotopyExtension φ D S =
      scalarPerfectClosedExtension φ D S ⋙
        toHomotopy A' (PerfectDGModuleOver A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S)) :=
  CategoryTheory.Quotient.lift_spec _ _ _

def scalarPerfectClosedDerivedIso (S : Set D) :
    (perfectDGModuleInclusion A D S).onClosed ⋙ moduleToDerived A D ⋙
        ScalarExtension.derivedExtension φ D ≅
      scalarPerfectClosedExtension φ D S ⋙
        (perfectDGModuleInclusion A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S)).onClosed ⋙
            moduleToDerived A' (ScalarExtension.DGBaseChange φ D) := by
  let I := (perfectDGModuleInclusion A D S).onClosed
  let a := Functor.whiskerLeft I (ScalarExtension.derivedExtensionAugmentation φ D)
  have (M : ClosedCategory A (PerfectDGModuleOver A D S)) : IsIso (a.app M) :=
    scalarDerivedExtensionAugmentation_isIso_of_projective φ D (I.obj M)
      (ForgetEnrichment.to (Complex A) M).property.1
  have : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a ≪≫ Functor.isoWhiskerRight (scalarPerfectClosedInclusionIso φ D S).symm
    (moduleToDerived A' (ScalarExtension.DGBaseChange φ D))

end SerrePositivity.DifferentialGraded
end

end ScalarEnhancementClosed

/-! ## ScalarEnhancementDerivedComparison（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarEnhancementDerivedComparison.lean） -/

/-! # U13 enhancementの実際の係数拡大と主Perfの導来係数拡大の比較 -/

@[expose] public section ScalarEnhancementDerivedComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

def scalarPerfectHomotopyDerivedIso (S : Set D) :
    perfectDGModuleToDerived A D S ⋙ ScalarExtension.derivedExtension φ D ≅
      scalarPerfectHomotopyExtension φ D S ⋙
        perfectDGModuleToDerived A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S) := by
  let I := (perfectDGModuleInclusion A D S).onClosed
  let J := (perfectDGModuleInclusion A' (ScalarExtension.DGBaseChange φ D)
    (scalarPerfectGenerators φ D S)).onClosed
  let C := scalarPerfectClosedExtension φ D S
  let e := Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft I (moduleToHomotopyDerivedIso A D))
      (ScalarExtension.derivedExtension φ D) ≪≫
    scalarPerfectClosedDerivedIso φ D S ≪≫
      (Functor.isoWhiskerLeft (C ⋙ J)
        (moduleToHomotopyDerivedIso A' (ScalarExtension.DGBaseChange φ D))).symm
  exact CategoryTheory.Quotient.natIsoLift _ e

/-- 実際のH⁰係数拡大と、受入済み導来係数拡大の主Perfへの制限はU13の比較と可換。 -/
def scalarPerfectHomotopyComparison (S : Set D) :
    perfectDGModuleToPerfect A D S ⋙ perfectScalarDerivedExtension φ D S ≅
      scalarPerfectHomotopyExtension φ D S ⋙
        perfectDGModuleToPerfect A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S) :=
  (((modulePerfectOver A' (ScalarExtension.DGBaseChange φ D)
    (scalarPerfectGenerators φ D S)).fullyFaithfulι).whiskeringRight _).preimageIso
        (scalarPerfectHomotopyDerivedIso φ D S)

end SerrePositivity.DifferentialGraded
end

end ScalarEnhancementDerivedComparison

/-! ## ScalarEnhancementShift（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarEnhancementShift.lean） -/

/-! # U13 enhancementの実際の係数変更のshiftと三角性 -/

@[expose] public section ScalarEnhancementShift

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

def scalarPerfectHomotopyInclusionIso (S : Set D) :
    scalarPerfectHomotopyExtension φ D S ⋙
        (perfectDGModuleInclusion A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S)).onHomotopy ≅
      (perfectDGModuleInclusion A D S).onHomotopy ⋙ scalarModuleExtensionHomotopy φ D :=
  Quotient.natIsoLift _ (Functor.isoWhiskerRight (scalarPerfectClosedInclusionIso φ D S)
    (moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D)))

local instance (S : Set D) : (perfectDGModuleInclusion A D S).onHomotopy.CommShift ℤ :=
  perfectDGModuleInclusionHomotopyCommShift A D S
local instance (S : Set (ScalarExtension.DGBaseChange φ D)) :
    (perfectDGModuleInclusion A' (ScalarExtension.DGBaseChange φ D) S).onHomotopy.CommShift ℤ :=
  perfectDGModuleInclusionHomotopyCommShift A' (ScalarExtension.DGBaseChange φ D) S
local instance : (scalarModuleExtensionHomotopy φ D).CommShift ℤ :=
  scalarModuleExtensionHomotopyCommShift φ D

@[instance_reducible]
def scalarPerfectHomotopyExtensionCommShift (S : Set D) :
    (scalarPerfectHomotopyExtension φ D S).CommShift ℤ :=
  Functor.CommShift.ofComp (scalarPerfectHomotopyInclusionIso φ D S) ℤ

lemma scalarPerfectHomotopyInclusionIso_commShift (S : Set D) :
    letI := scalarPerfectHomotopyExtensionCommShift φ D S
    NatTrans.CommShift (scalarPerfectHomotopyInclusionIso φ D S).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (scalarPerfectHomotopyInclusionIso φ D S) ℤ

lemma scalarPerfectHomotopyExtensionIsTriangulated (S : Set D) :
    letI := scalarPerfectHomotopyExtensionCommShift φ D S
    (scalarPerfectHomotopyExtension φ D S).IsTriangulated := by
  let := scalarPerfectHomotopyExtensionCommShift φ D S
  let := scalarPerfectHomotopyInclusionIso_commShift φ D S
  let := perfectDGModuleInclusionHomotopyIsTriangulated A D S
  let := perfectDGModuleInclusionHomotopyIsTriangulated A'
    (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S)
  let := scalarModuleExtensionHomotopyIsTriangulated φ D
  exact (Functor.isTriangulated_iff_comp_right (scalarPerfectHomotopyInclusionIso φ D S)).2
    inferInstance

end SerrePositivity.DifferentialGraded
end

end ScalarEnhancementShift

/-! ## ScalarPerfectShiftTriangles（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarPerfectShiftTriangles.lean） -/

/-! # 受入済みの主Perf係数変更の整合的shift・三角性 -/

@[expose] public section ScalarPerfectShiftTriangles

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

def scalarPerfectDerivedTransportIso (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).inverse ⋙
        (scalarPerfectHomotopyExtension φ D S ⋙
          perfectDGModuleToPerfect A' (ScalarExtension.DGBaseChange φ D)
            (scalarPerfectGenerators φ D S)) ≅ perfectScalarDerivedExtension φ D S :=
  Functor.isoWhiskerLeft (perfectDGModuleHomotopyEquivalence A D S).inverse
      (scalarPerfectHomotopyComparison φ D S).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectDGModuleHomotopyEquivalence A D S).counitIso
      (perfectScalarDerivedExtension φ D S) ≪≫
    (perfectScalarDerivedExtension φ D S).leftUnitor

local instance (S : Set D) : (scalarPerfectHomotopyExtension φ D S).CommShift ℤ :=
  scalarPerfectHomotopyExtensionCommShift φ D S

@[instance_reducible]
def perfectScalarDerivedExtensionCommShift (S : Set D) :
    (perfectScalarDerivedExtension φ D S).CommShift ℤ :=
  Functor.CommShift.ofIso (scalarPerfectDerivedTransportIso φ D S) ℤ

lemma scalarPerfectDerivedTransportIso_commShift (S : Set D) :
    letI := perfectScalarDerivedExtensionCommShift φ D S
    NatTrans.CommShift (scalarPerfectDerivedTransportIso φ D S).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (scalarPerfectDerivedTransportIso φ D S) ℤ

lemma perfectScalarDerivedExtensionIsTriangulated (S : Set D) :
    letI := perfectScalarDerivedExtensionCommShift φ D S
    (perfectScalarDerivedExtension φ D S).IsTriangulated := by
  let := perfectScalarDerivedExtensionCommShift φ D S
  let := scalarPerfectDerivedTransportIso_commShift φ D S
  let := scalarPerfectHomotopyExtensionIsTriangulated φ D S
  have : ((perfectDGModuleHomotopyEquivalence A D S).inverse ⋙
      (scalarPerfectHomotopyExtension φ D S ⋙
        perfectDGModuleToPerfect A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S))).IsTriangulated := inferInstance
  exact Functor.isTriangulated_of_iso (scalarPerfectDerivedTransportIso φ D S)

/-- U13同値の単位を用いて正規化した主Perfの係数変更正方形。 -/
def scalarPerfectHomotopyShiftComparison (S : Set D) :
    perfectDGModuleToPerfect A D S ⋙ perfectScalarDerivedExtension φ D S ≅
      scalarPerfectHomotopyExtension φ D S ⋙
        perfectDGModuleToPerfect A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S) :=
  Functor.isoWhiskerLeft (perfectDGModuleToPerfect A D S)
      (scalarPerfectDerivedTransportIso φ D S).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectDGModuleHomotopyEquivalence A D S).unitIso.symm _ ≪≫
    Functor.leftUnitor _

lemma scalarPerfectHomotopyShiftComparison_eq (S : Set D) :
    scalarPerfectHomotopyShiftComparison φ D S = scalarPerfectHomotopyComparison φ D S := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  dsimp [scalarPerfectHomotopyShiftComparison, scalarPerfectDerivedTransportIso]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  let e := perfectDGModuleHomotopyEquivalence A D S
  let G := perfectScalarDerivedExtension φ D S
  let H := scalarPerfectHomotopyExtension φ D S ⋙
    perfectDGModuleToPerfect A' (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S)
  let α : e.functor ⋙ G ≅ H := scalarPerfectHomotopyComparison φ D S
  change G.map (e.counitIso.inv.app (e.functor.obj X)) ≫
    α.hom.app (e.inverse.obj (e.functor.obj X)) ≫ H.map (e.unitIso.inv.app X) = α.hom.app X
  rw [← α.hom.naturality, Functor.comp_map, ← Category.assoc, ← G.map_comp,
    e.counitInv_functor_comp]
  exact (congrArg (fun k => k ≫ α.hom.app X) (G.map_id (e.functor.obj X))).trans
    (Category.id_comp _)

lemma scalarPerfectHomotopyShiftComparison_commShift (S : Set D) :
    letI := perfectScalarDerivedExtensionCommShift φ D S
    NatTrans.CommShift (scalarPerfectHomotopyShiftComparison φ D S).hom ℤ := by
  let := perfectScalarDerivedExtensionCommShift φ D S
  let := scalarPerfectDerivedTransportIso_commShift φ D S
  unfold scalarPerfectHomotopyShiftComparison
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

lemma scalarPerfectHomotopyComparison_commShift (S : Set D) :
    letI := perfectScalarDerivedExtensionCommShift φ D S
    NatTrans.CommShift (scalarPerfectHomotopyComparison φ D S).hom ℤ := by
  let := perfectScalarDerivedExtensionCommShift φ D S
  rw [← scalarPerfectHomotopyShiftComparison_eq φ D S]
  exact scalarPerfectHomotopyShiftComparison_commShift φ D S

def scalarPerfectHomotopyTriangleSquareIso (S : Set D) :
    letI := perfectScalarDerivedExtensionCommShift φ D S
    (perfectDGModuleToPerfect A D S).mapTriangle ⋙
        (perfectScalarDerivedExtension φ D S).mapTriangle ≅
      (scalarPerfectHomotopyExtension φ D S).mapTriangle ⋙
        (perfectDGModuleToPerfect A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S)).mapTriangle := by
  letI := perfectScalarDerivedExtensionCommShift φ D S
  let := scalarPerfectHomotopyComparison_commShift φ D S
  exact (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (scalarPerfectHomotopyComparison φ D S) ≪≫
      Functor.mapTriangleCompIso _ _

end SerrePositivity.DifferentialGraded
end

end ScalarPerfectShiftTriangles
