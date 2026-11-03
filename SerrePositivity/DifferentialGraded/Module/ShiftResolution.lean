module

public import SerrePositivity.DifferentialGraded.Module.Disk
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Module.Graded
public import Mathlib.CategoryTheory.Shift.Quotient
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import SerrePositivity.DifferentialGraded.Module.TensorFree
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import SerrePositivity.DifferentialGraded.Module.ActionLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-!
# Module.ShiftResolution

## 概要
22 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## KernelCells（旧 SerrePositivity/DifferentialGraded/Module/KernelCells.lean） -/

/-! # kernelの全cycleを添字とするcell付加の一段階 -/

@[expose] public section KernelCells
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma freeSphereHomEquiv_zero_val (x : D) (n : ℤ) (M : ModuleCategory A D) :
    (freeSphereHomEquiv A D x n M (0 : freeSphere A D x n ⟶ M)).val = 0 := by
  have h := freeSphereHomEquiv_naturality_val A D x n (𝟙 (freeSphere A D x n))
    (0 : freeSphere A D x n ⟶ M)
  rw [Category.id_comp, CategoryTheory.Functor.map_zero, HomologicalComplex.zero_f] at h
  exact h

/-- 全対象・次数のkernel内のcycle。次数nのcellはこの次数n+1のcycleを消す。 -/
def ModuleKernelCellIndex {M N : ModuleCategory A D} (f : M ⟶ N) :=
  Σ x : D, Σ n : ℤ,
    { z : complexCycles A ((moduleEvaluation A D x).obj M) (n + 1) //
      ((moduleEvaluation A D x).map f).f (n + 1) z.val = 0 }

instance moduleKernelCellIndexSmall {M N : ModuleCategory A D} (f : M ⟶ N) :
    Small.{u} (ModuleKernelCellIndex A D f) := by
  unfold ModuleKernelCellIndex
  infer_instance

def moduleKernelCellFamily {M N : ModuleCategory A D} (f : M ⟶ N) :
    ModuleKernelCellIndex A D f → ModuleCategory A D := fun j => freeSphere A D j.1 (j.2.1 + 1)

def moduleKernelCellSource {M N : ModuleCategory A D} (f : M ⟶ N) : ModuleCategory A D :=
  ∐ moduleKernelCellFamily A D f

def moduleKernelCellMap {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleKernelCellSource A D f ⟶ M :=
  Sigma.desc (fun j : ModuleKernelCellIndex A D f =>
    (freeSphereHomEquiv A D j.1 (j.2.1 + 1) M).symm j.2.2.val)

@[reassoc] lemma moduleKernelCellι_map {M N : ModuleCategory A D} (f : M ⟶ N)
    (j : ModuleKernelCellIndex A D f) :
    Sigma.ι (moduleKernelCellFamily A D f) j ≫ moduleKernelCellMap A D f =
      (freeSphereHomEquiv A D j.1 (j.2.1 + 1) M).symm j.2.2.val :=
  Sigma.ι_comp_desc _ _

lemma moduleKernelCellMap_comp {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleKernelCellMap A D f ≫ f = 0 := by
  apply Sigma.hom_ext
  intro j
  have hz : (freeSphereHomEquiv A D j.1 (j.2.1 + 1) M).symm j.2.2.val ≫ f = 0 := by
    apply (freeSphereHomEquiv A D j.1 (j.2.1 + 1) N).injective
    apply Subtype.ext
    have hn := freeSphereHomEquiv_naturality_val A D j.1 (j.2.1 + 1)
      ((freeSphereHomEquiv A D j.1 (j.2.1 + 1) M).symm j.2.2.val) f
    have he := congrArg (fun c => ((moduleEvaluation A D j.1).map f).f (j.2.1 + 1) c.val)
      ((freeSphereHomEquiv A D j.1 (j.2.1 + 1) M).apply_symm_apply j.2.2.val)
    exact hn.trans (he.trans (j.2.2.property.trans
      (freeSphereHomEquiv_zero_val A D j.1 (j.2.1 + 1) N).symm))
  calc
    Sigma.ι (moduleKernelCellFamily A D f) j ≫ (moduleKernelCellMap A D f ≫ f) =
        (Sigma.ι (moduleKernelCellFamily A D f) j ≫ moduleKernelCellMap A D f) ≫ f :=
      (Category.assoc _ _ _).symm
    _ = (freeSphereHomEquiv A D j.1 (j.2.1 + 1) M).symm j.2.2.val ≫ f :=
      congrArg (fun k => k ≫ f) (moduleKernelCellι_map A D f j)
    _ = 0 := hz
    _ = Sigma.ι (moduleKernelCellFamily A D f) j ≫ 0 := comp_zero.symm

def moduleKernelCellStep {M N : ModuleCategory A D} (f : M ⟶ N) : ModuleCategory A D :=
  moduleCone A D (moduleKernelCellMap A D f)

def moduleKernelCellStepι {M N : ModuleCategory A D} (f : M ⟶ N) :
    M ⟶ moduleKernelCellStep A D f := moduleConeInr A D (moduleKernelCellMap A D f)

def moduleKernelCellStepπ {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleKernelCellStep A D f ⟶ N :=
  moduleConeDesc A D (moduleKernelCellMap A D f) f (moduleKernelCellMap_comp A D f)

@[reassoc] lemma moduleKernelCellStep_fac {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleKernelCellStepι A D f ≫ moduleKernelCellStepπ A D f = f :=
  moduleConeDesc_inr A D _ _ _

lemma moduleKernelCellStepπ_degreewiseSurjective {M N : ModuleCategory A D} (f : M ⟶ N)
    (hf : moduleDegreewiseSurjective A D f) :
    moduleDegreewiseSurjective A D (moduleKernelCellStepπ A D f) := by
  intro x n y
  obtain ⟨t, ht⟩ := hf x n y
  refine ⟨((moduleEvaluation A D x).map (moduleKernelCellStepι A D f)).f n t, ?_⟩
  have h := congrArg (fun k => ((moduleEvaluation A D x).map k).f n t)
    (moduleKernelCellStep_fac A D f)
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] at h
  exact h.trans ht

/-- kernelの各cycleの像を、一段階のcell付加で境界にする。 -/
lemma moduleKernelCellStep_killsInKernel {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) (n : ℤ)
    (z : complexCycles A ((moduleEvaluation A D x).obj M) (n + 1))
    (hz : ((moduleEvaluation A D x).map f).f (n + 1) z.val = 0) :
    ∃ t : ((moduleEvaluation A D x).obj (moduleKernelCellStep A D f)).X n,
      ((moduleEvaluation A D x).obj (moduleKernelCellStep A D f)).d n (n + 1) t =
        ((moduleEvaluation A D x).map (moduleKernelCellStepι A D f)).f (n + 1) z.val ∧
      ((moduleEvaluation A D x).map (moduleKernelCellStepπ A D f)).f n t = 0 := by
  let j : ModuleKernelCellIndex A D f := ⟨x, n, ⟨z, hz⟩⟩
  let a := Sigma.ι (moduleKernelCellFamily A D f) j
  let c := freeSphereHomEquiv A D x (n + 1) (moduleKernelCellSource A D f) a
  have hv : ((moduleEvaluation A D x).map (moduleKernelCellMap A D f)).f (n + 1) c.val = z.val := by
    have h : a ≫ moduleKernelCellMap A D f = (freeSphereHomEquiv A D x (n + 1) M).symm z :=
      moduleKernelCellι_map A D f j
    have he := congrArg (fun k => (freeSphereHomEquiv A D x (n + 1) M k).val) h
    rw [freeSphereHomEquiv_naturality_val, Equiv.apply_symm_apply] at he
    exact he
  simp only [moduleKernelCellStepι, moduleConeInr_eval, moduleKernelCellStepπ, moduleConeDesc_eval]
  change ∃ t : (mappingCone ((moduleEvaluation A D x).map (moduleKernelCellMap A D f))).X n,
    (mappingCone ((moduleEvaluation A D x).map (moduleKernelCellMap A D f))).d n (n + 1) t =
      (mappingCone.inr ((moduleEvaluation A D x).map (moduleKernelCellMap A D f))).f
        (n + 1) z.val ∧ _
  refine ⟨complexConeBoundaryWitness ((moduleEvaluation A D x).map (moduleKernelCellMap A D f)) n c,
    ?_, ?_⟩
  · exact (complexConeBoundaryWitness_d _ n c).trans (congrArg _ hv)
  · exact complexConeBoundaryWitness_desc _ _ _ n c

lemma moduleKernelCellStep_kills {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) (n : ℤ)
    (z : complexCycles A ((moduleEvaluation A D x).obj M) (n + 1))
    (hz : ((moduleEvaluation A D x).map f).f (n + 1) z.val = 0) :
    ∃ t : ((moduleEvaluation A D x).obj (moduleKernelCellStep A D f)).X n,
      ((moduleEvaluation A D x).obj (moduleKernelCellStep A D f)).d n (n + 1) t =
        ((moduleEvaluation A D x).map (moduleKernelCellStepι A D f)).f (n + 1) z.val := by
  obtain ⟨t, ht, _⟩ := moduleKernelCellStep_killsInKernel A D f x n z hz
  exact ⟨t, ht⟩

end SerrePositivity.DifferentialGraded
end

end KernelCells

/-! ## ShiftHomotopy（旧 SerrePositivity/DifferentialGraded/Module/ShiftHomotopy.lean） -/

/-! # K(D) の整数 shift と quasiIso の保存 -/

@[expose] public section ShiftHomotopy
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleBoundaryCompatibleWithShift :
    (boundaryRelation A (RightModule A D)).IsCompatibleWithShift ℤ where
  condition s M N f g h := by
    have hs := (moduleShiftDG A D s).preserves_boundary f g h
    change boundaryRelation A (RightModule A D)
      ((moduleShiftFunctor A D s).map f) ((moduleShiftFunctor A D s).map g)
    rw [← moduleShiftDG_onClosed_eq]
    exact hs

/-- 全 dg 自然な加群ホモトピーはすべての整数 shift で保存される。 -/
lemma moduleHomotopy_shift {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) (s : ℤ) :
    Nonempty (ModuleHomotopy A D (f⟦s⟧') (g⟦s⟧')) := by
  apply (moduleHomotopy_nonempty_iff A D _ _).2
  exact HomRel.IsCompatibleWithShift.condition s f g
    ((moduleHomotopy_nonempty_iff A D f g).1 ⟨h⟩)

-- Mathlib の商 shift は元の zero/add coherence を運ぶ。
instance moduleHomotopyEvaluationCommShift (x : D) :
    (moduleHomotopyEvaluation A D x).CommShift ℤ := by
  unfold moduleHomotopyEvaluation
  infer_instance

/-- 閉零加群の準同型判定は整数 shift で不変。 -/
lemma moduleQuasiIso_shift_iff {M N : ModuleCategory A D} (f : M ⟶ N) (s : ℤ) :
    moduleQuasiIso A D (f⟦s⟧') ↔ moduleQuasiIso A D f := by
  simp only [moduleQuasiIso_iff]
  apply forall_congr'
  intro x
  change QuasiIso ((moduleEvaluation A D x).map (moduleShiftMap A D s f)) ↔ _
  rw [moduleShiftMap_eval]
  exact CochainComplex.quasiIso_shift_iff _ s

instance moduleQuasiIsoCompatibleWithShift : (moduleQuasiIso A D).IsCompatibleWithShift ℤ where
  condition s := by
    ext M N f
    exact moduleQuasiIso_shift_iff A D f s

/-- K(D) の準同型判定も整数 shift で不変。評価の CommShift を使用する。 -/
lemma moduleHomotopyQuasiIso_shift_iff {M N : ModuleHomotopyCategory A D}
    (f : M ⟶ N) (s : ℤ) :
    moduleHomotopyQuasiIso A D (f⟦s⟧') ↔ moduleHomotopyQuasiIso A D f := by
  change (∀ x : D, _root_.HomotopyCategory.quasiIso (ModuleCat A) (.up ℤ)
    ((moduleHomotopyEvaluation A D x).map (f⟦s⟧'))) ↔ _
  apply forall_congr'
  intro x
  let W := _root_.HomotopyCategory.quasiIso (ModuleCat A) (.up ℤ)
  let E := moduleHomotopyEvaluation A D x
  have hi := W.arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso (E.commShiftIso s)).app (Arrow.mk f))
  change W (E.map (f⟦s⟧')) ↔ W ((E.map f)⟦s⟧') at hi
  exact hi.trans (MorphismProperty.IsCompatibleWithShift.iff W (E.map f) s)

instance moduleHomotopyQuasiIsoCompatibleWithShift :
    (moduleHomotopyQuasiIso A D).IsCompatibleWithShift ℤ where
  condition s := by
    ext M N f
    exact moduleHomotopyQuasiIso_shift_iff A D f s

end SerrePositivity.DifferentialGraded
end

end ShiftHomotopy

/-! ## ShiftHomotopyComparison（旧 SerrePositivity/DifferentialGraded/Module/ShiftHomotopyComparison.lean） -/

/-! # 全Hom dg shiftと既存K(D)の整数shiftとの自然比較 -/

@[expose] public section ShiftHomotopyComparison
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 実際のdg shiftのH⁰関手は、既存の商圏shiftと自然同型で一致する。 -/
def moduleShiftDGHomotopyIso (s : ℤ) :
    (moduleShiftDG A D s).onHomotopy ≅ shiftFunctor (ModuleHomotopyCategory A D) s :=
  Quotient.natIsoLift (boundaryRelation A (RightModule A D))
    (eqToIso ((moduleShiftDG A D s).onHomotopy_fac) ≪≫
      Functor.isoWhiskerRight (eqToIso (moduleShiftDG_onClosed_eq A D s)) (moduleToHomotopy A D) ≪≫
      (moduleToHomotopy A D).commShiftIso s)

end SerrePositivity.DifferentialGraded
end

end ShiftHomotopyComparison

/-! ## ShiftCompatibility（旧 SerrePositivity/DifferentialGraded/Module/ShiftCompatibility.lean） -/

/-! # 商shiftの加法性と評価でのshift交換同型 -/

@[expose] public section ShiftCompatibility
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleHomotopyShiftAdditive (s : ℤ) :
    (shiftFunctor (ModuleHomotopyCategory A D) s).Additive := by
  let Q := moduleToHomotopy A D
  let : (Q ⋙ shiftFunctor (ModuleHomotopyCategory A D) s).Additive :=
    Functor.additive_of_iso (Q.commShiftIso s)
  exact Functor.additive_of_full_essSurj_comp Q _

lemma moduleEvaluation_shiftComm (M : ModuleCategory A D) (s t : ℤ) (x : D) :
    (moduleEvaluation A D x).map
      ((shiftFunctorComm (ModuleCategory A D) s t).hom.app M) =
        (shiftFunctorComm (Complex A) s t).hom.app ((moduleEvaluation A D x).obj M) := by
  have h := (moduleEvaluation A D x).map_shiftFunctorComm_hom_app M s t
  change (moduleEvaluation A D x).map
    ((shiftFunctorComm (ModuleCategory A D) s t).hom.app M) =
      𝟙 _ ≫ (𝟙 _)⟦t⟧' ≫
        (shiftFunctorComm (Complex A) s t).hom.app ((moduleEvaluation A D x).obj M) ≫
          (𝟙 _)⟦s⟧' ≫ 𝟙 _ at h
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at h
  exact h.trans (Category.comp_id _)

end SerrePositivity.DifferentialGraded
end

end ShiftCompatibility

/-! ## ShiftComparisonEvaluation（旧 SerrePositivity/DifferentialGraded/Module/ShiftComparisonEvaluation.lean） -/

/-! # dg加群shiftの商比較を実際の閉零代表で評価する -/

@[expose] public section ShiftComparisonEvaluation
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 商比較の抽象的な評価式を使い、全Hom shiftのH⁰比較を元の商shiftの成分に戻す。 -/
lemma moduleShiftDGHomotopyIso_closed_hom_app (s : ℤ) (M : ModuleCategory A D) :
    (moduleShiftDGHomotopyIso A D s).hom.app ((moduleToHomotopy A D).obj M) =
      ((moduleToHomotopy A D).commShiftIso s).hom.app M := by
  have h := quotientComparison_hom_app (boundaryRelation A (RightModule A D))
    (moduleShiftDG A D s).onHomotopy (shiftFunctor (ModuleHomotopyCategory A D) s)
    (moduleShiftDG A D s).onClosed (moduleShiftFunctor A D s) (moduleToHomotopy A D)
    (moduleShiftDG A D s).onHomotopy_fac (moduleShiftDG_onClosed_eq A D s)
    ((moduleToHomotopy A D).commShiftIso s) M
  have h' : (moduleShiftDGHomotopyIso A D s).hom.app ((moduleToHomotopy A D).obj M) =
      𝟙 ((moduleToHomotopy A D).obj (M⟦s⟧)) ≫
        (moduleToHomotopy A D).map (𝟙 (M⟦s⟧)) ≫
          ((moduleToHomotopy A D).commShiftIso s).hom.app M := h
  let f := ((moduleToHomotopy A D).commShiftIso s).hom.app M
  have hi := (moduleToHomotopy A D).map_id (M⟦s⟧)
  exact h'.trans ((Category.id_comp _).trans
    ((congrArg (fun g => g ≫ f) hi).trans (Category.id_comp f)))

end SerrePositivity.DifferentialGraded
end

end ShiftComparisonEvaluation

/-! ## Basic（旧 SerrePositivity/DifferentialGraded/Module/Semifree/Basic.lean） -/

/-! # 証明付きsemifree filtration

自由sphere余積の表示、全斉次作用に関する分裂、余極限の網羅性をデータとして保持する。
-/

@[expose] public section Basic
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- u-smallな自由sphere余積としての具体的表示。添字のambient宇宙はmax u v。 -/
structure ModuleSphereFreePresentation (M : ModuleCategory A D) where
  Index : Type (max u v)
  [smallIndex : Small.{u} Index]
  object : Index → D
  degree : Index → ℤ
  iso : M ≅ ∐ (fun t => freeSphere A D (object t) (degree t))

/-- 初期段と各商が自由sphere余積であり、全次数で分裂する網羅的filtration。 -/
structure ModuleSemifreeFiltration (M : ModuleCategory A D) where
  stage : ℕ → ModuleCategory A D
  transition : ∀ n, stage n ⟶ stage (n + 1)
  initial : ModuleSphereFreePresentation A D (stage 0)
  quotient : ℕ → ModuleCategory A D
  quotientMap : ∀ n, stage (n + 1) ⟶ quotient n
  split : ∀ n, ModuleGradedSplit A D (transition n) (quotientMap n)
  quotientPresentation : ∀ n, ModuleSphereFreePresentation A D (quotient n)
  cocone : Cocone (Functor.ofSequence transition)
  isColimit : IsColimit cocone
  iso : cocone.pt ≅ M

/-- この主dg加群はsemifree filtrationを持つ。 -/
def moduleSemifree : ObjectProperty (ModuleCategory A D) :=
  fun M => Nonempty (ModuleSemifreeFiltration A D M)

/-- 各商は主圏での真のcokernelであり、単なる次数付き表示ではない。 -/
def ModuleSemifreeFiltration.stepCokernel {M : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (F.quotientMap n) (F.split n).inclusion_projection) :=
  moduleGradedSplitCokernel A D (F.split n)

end SerrePositivity.DifferentialGraded
end

end Basic

/-! ## FreeSphereShift（旧 SerrePositivity/DifferentialGraded/Module/FreeSphereShift.lean） -/

/-! # 自由sphereの整数shift -/

@[expose] public section FreeSphereShift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- コチェイン規約：sphere nのshift sはsphere (n-s)。 -/
def complexSphereShiftIso (n s : ℤ) : (complexSphere A n)⟦s⟧ ≅ complexSphere A (n - s) :=
  ((CochainComplex.singleFunctors (ModuleCat.{u} A)).shiftIso s (n - s) n (by omega)).app
    (𝟙_ (ModuleCat A))

/-- 自由sphereのshiftを主dg加群圏で同定する。 -/
def freeSphereShiftIso (x : D) (n s : ℤ) :
    (freeSphere A D x n)⟦s⟧ ≅ freeSphere A D x (n - s) :=
  (freeAtShiftIso A D x (complexSphere A n) s).symm ≪≫
    (freeAt x).mapIso (complexSphereShiftIso A n s)

end SerrePositivity.DifferentialGraded
end

end FreeSphereShift

/-! ## ShiftCoproduct（旧 SerrePositivity/DifferentialGraded/Module/ShiftCoproduct.lean） -/

/-! # shiftされた自由sphereの余積

shiftの余積保存はMathlibの同値関手の一般論から再利用する。
-/

@[expose] public section ShiftCoproduct
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Small.{u} J]

/-- 主加群圏の整数shiftとu-small余積の比較。 -/
def moduleShiftCoproductIso (M : J → ModuleCategory A D) (s : ℤ) :
    (∐ M)⟦s⟧ ≅ ∐ (fun t => (M t)⟦s⟧) :=
  PreservesCoproduct.iso (CategoryTheory.shiftFunctor (ModuleCategory A D) s) M

/-- shiftされた自由sphereの余積も自由sphereの余積。 -/
def freeSphereCoproductShiftIso (x : J → D) (n : J → ℤ) (s : ℤ) :
    (∐ fun t => freeSphere A D (x t) (n t))⟦s⟧ ≅
      ∐ fun t => freeSphere A D (x t) (n t - s) :=
  moduleShiftCoproductIso A D (fun t => freeSphere A D (x t) (n t)) s ≪≫
    Limits.Sigma.mapIso (fun t => freeSphereShiftIso A D (x t) (n t) s)

end SerrePositivity.DifferentialGraded
end

end ShiftCoproduct

/-! ## ConeShiftSquares（旧 SerrePositivity/DifferentialGraded/Module/ConeShiftSquares.lean） -/

/-! # cone shift比較と符号付き可換square -/

@[expose] public section ConeShiftSquares
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleShiftSignSquare (s : ℤ) {X Y : ModuleCategory A D} (f : X ⟶ Y) :
    (s.negOnePow • f) ≫ (s.negOnePow • 𝟙 Y) = 𝟙 X ≫ f := by
  simp only [Linear.comp_units_smul, Category.comp_id, Category.id_comp, smul_smul,
    Int.units_mul_self, one_smul]

def moduleShiftSignIso (s : ℤ) (X : ModuleCategory A D) : X ≅ X where
  hom := s.negOnePow • 𝟙 X
  inv := s.negOnePow • 𝟙 X
  hom_inv_id := (moduleShiftSignSquare A D s (𝟙 X)).trans (Category.id_comp _)
  inv_hom_id := (moduleShiftSignSquare A D s (𝟙 X)).trans (Category.id_comp _)

lemma moduleEvaluation_sign_map (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (s.negOnePow • f) =
      s.negOnePow • (moduleEvaluation A D x).map f :=
  (moduleEvaluation A D x).map_units_smul s.negOnePow f

lemma moduleConeShift_inr (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (s.negOnePow • moduleShiftMap A D s (moduleConeInr A D f)) ≫
      moduleConeShiftHom A D s f =
        (s.negOnePow • 𝟙 (moduleShiftObj A D s N)) ≫
          moduleConeInr A D (moduleShiftMap A D s f) := by
  apply moduleMorphism_ext
  intro x
  rw [(moduleEvaluation A D x).map_comp]
  conv_rhs => rw [(moduleEvaluation A D x).map_comp]
  rw [moduleEvaluation_sign_map A D s (moduleShiftMap A D s (moduleConeInr A D f)) x,
    moduleEvaluation_sign_map A D s (𝟙 (moduleShiftObj A D s N)) x,
    (moduleEvaluation A D x).map_id, moduleShiftMap_eval, moduleConeInr_eval,
    moduleConeShiftHom_eval, moduleConeInr_eval]
  exact complexConeShift_inr ((moduleEvaluation A D x).map f) s _
    (moduleShiftMap_eval A D s f x)

lemma moduleConeShift_connecting (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    s.negOnePow • (moduleShiftMap A D s (moduleConeConnecting A D f) ≫
      (shiftFunctorComm (ModuleCategory A D) 1 s).hom.app M) =
        moduleConeShiftHom A D s f ≫ moduleConeConnecting A D (moduleShiftMap A D s f) := by
  apply moduleMorphism_ext
  intro x
  let E := moduleEvaluation A D x
  have h₁ := (moduleShiftMap_eval A D s (moduleConeConnecting A D f) x).trans
    (congrArg (fun a => (CategoryTheory.shiftFunctor (Complex A) s).map a)
      (moduleConeConnecting_eval A D f x))
  let c := (shiftFunctorComm (Complex A) 1 s).hom.app (E.obj M)
  have h₂ := (E.map_comp (moduleShiftMap A D s (moduleConeConnecting A D f))
    ((shiftFunctorComm (ModuleCategory A D) 1 s).hom.app M)).trans
      ((congrArg (fun b => E.map (moduleShiftMap A D s (moduleConeConnecting A D f)) ≫ b)
        (moduleEvaluation_shiftComm A D M 1 s x)).trans
          (congrArg (fun a => a ≫ c) h₁))
  have hL := (moduleEvaluation_sign_map A D s
    (moduleShiftMap A D s (moduleConeConnecting A D f) ≫
      (shiftFunctorComm (ModuleCategory A D) 1 s).hom.app M) x).trans
        (congrArg (s.negOnePow • ·) h₂)
  have hR := (E.map_comp (moduleConeShiftHom A D s f)
    (moduleConeConnecting A D (moduleShiftMap A D s f))).trans
      (congrArg₂ (fun a b => a ≫ b) (moduleConeShiftHom_eval A D s f x)
        (moduleConeConnecting_eval A D (moduleShiftMap A D s f) x))
  exact hL.trans (((Linear.units_smul_comp _ _ _).symm.trans
    (complexConeShift_connecting (E.map f) s _
      (moduleShiftMap_eval A D s f x))).trans hR.symm)

end SerrePositivity.DifferentialGraded
end

end ConeShiftSquares

/-! ## ConeShiftTriangleOrdinary（旧 SerrePositivity/DifferentialGraded/Module/ConeShiftTriangleOrdinary.lean） -/

/-! # 標準cone三角形の整数shift比較 -/

@[expose] public section ConeShiftTriangleOrdinary
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 明示的な加群shift射を可換条件として受け取る三角形shiftの同型構成子。 -/
def moduleTriangleShiftIsoMk (s : ℤ) (T T' : Triangle (ModuleCategory A D))
    (e₁ : moduleShiftObj A D s T.obj₁ ≅ T'.obj₁)
    (e₂ : moduleShiftObj A D s T.obj₂ ≅ T'.obj₂)
    (e₃ : moduleShiftObj A D s T.obj₃ ≅ T'.obj₃)
    (h₁ : (s.negOnePow • moduleShiftMap A D s T.mor₁) ≫ e₂.hom = e₁.hom ≫ T'.mor₁)
    (h₂ : (s.negOnePow • moduleShiftMap A D s T.mor₂) ≫ e₃.hom = e₂.hom ≫ T'.mor₂)
    (h₃ : (s.negOnePow • (moduleShiftMap A D s T.mor₃ ≫
      (shiftFunctorComm (ModuleCategory A D) 1 s).hom.app T.obj₁)) ≫ e₁.hom⟦(1 : ℤ)⟧' =
        e₃.hom ≫ T'.mor₃) :
    (Triangle.shiftFunctor (ModuleCategory A D) s).obj T ≅ T' :=
  by
    refine Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_
    · dsimp only [Triangle.shiftFunctor, Triangle.mk, moduleShiftFunctor_eq,
        moduleShiftFunctor] at h₁ ⊢
      exact h₁
    · dsimp only [Triangle.shiftFunctor, Triangle.mk, moduleShiftFunctor_eq,
        moduleShiftFunctor] at h₂ ⊢
      exact h₂
    · dsimp only [Triangle.shiftFunctor, Triangle.mk, moduleShiftFunctor_eq,
        moduleShiftFunctor] at h₃ ⊢
      exact h₃

lemma moduleConeShift_connecting_id (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (s.negOnePow • (moduleShiftMap A D s (moduleConeConnecting A D f) ≫
      (shiftFunctorComm (ModuleCategory A D) 1 s).hom.app M)) ≫
        (𝟙 (moduleShiftObj A D s M))⟦(1 : ℤ)⟧' =
          moduleConeShiftHom A D s f ≫ moduleConeConnecting A D (moduleShiftMap A D s f) := by
  have hi := (CategoryTheory.shiftFunctor (ModuleCategory A D) (1 : ℤ)).map_id
    (moduleShiftObj A D s M)
  exact (congrArg (fun a => (s.negOnePow •
    (moduleShiftMap A D s (moduleConeConnecting A D f) ≫
      (shiftFunctorComm (ModuleCategory A D) 1 s).hom.app M)) ≫ a) hi).trans
        ((Category.comp_id _).trans (moduleConeShift_connecting A D s f))

def moduleConeTriangleShiftIso (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (Triangle.shiftFunctor (ModuleCategory A D) s).obj (moduleConeTriangle A D f) ≅
      moduleConeTriangle A D (moduleShiftMap A D s f) :=
  moduleTriangleShiftIsoMk A D s (moduleConeTriangle A D f)
    (moduleConeTriangle A D (moduleShiftMap A D s f))
    (Iso.refl (moduleShiftObj A D s M))
    (moduleShiftSignIso A D s (moduleShiftObj A D s N)) (moduleConeShiftIso A D s f)
    (moduleShiftSignSquare A D s (moduleShiftMap A D s f))
    (moduleConeShift_inr A D s f) (moduleConeShift_connecting_id A D s f)


end SerrePositivity.DifferentialGraded
end

end ConeShiftTriangleOrdinary

/-! ## LeftShiftElements（旧 SerrePositivity/DifferentialGraded/Module/LeftShiftElements.lean） -/

/-! # 主Hom endの始域だけをshiftする斉次要素

成分はMathlibのleftShiftそのもの。次数はqからq+sへ移り、微分に(-1)^sを伴う。
-/

@[expose] public section LeftShiftElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomLeftShift_naturality (s : ℤ) {M N : RightModule A D} {q q' : ℤ}
    (hqq' : q + s = q') (z : (moduleHom A D M N).X q)
    (x y : Dᵒᵖ) (p : ℤ) (a : GradedHom A x y p) :
    (((shiftModule s M).map x y).f p a).comp
      (((moduleHomπ A D M N y.unop).f q z).leftShift s q' hqq') (by omega : p + q' = q' + p) =
      (q' * p).negOnePow •
        ((((moduleHomπ A D M N x.unop).f q z).leftShift s q' hqq').comp
          ((N.map x y).f p a) rfl) := by
  apply Cochain.ext
  intro i j hij
  rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ _ i (i + q') j rfl (by omega),
    shiftModule_map_v,
    Cochain.leftShift_v _ s q' hqq' (i + p) j (by omega) (i + p + s) (by omega),
    Cochain.leftShift_v _ s q' hqq' i (i + q') rfl (i + s) (by omega)]
  simp only [shiftFunctor_obj_X, Opposite.op_unop,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Category.id_comp,
    Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
  have hz := Cochain.congr_v (moduleHomElement_naturality A D q z x y p a)
    (i + s) j (by omega)
  rw [Cochain.comp_v _ _ _ (i + s) (i + p + s) j (by omega) (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ _ (i + s) (i + q') j (by omega) (by omega)] at hz
  rw [hz]
  simp only [smul_smul]
  congr 1
  simp only [← Int.negOnePow_add]
  congr 1
  rw [← hqq']
  ring

/-- 自然な次数qの要素を、始域shift後の次数q'へ移す。 -/
def moduleHomLeftShiftElement (s : ℤ) {M N : RightModule A D} {q q' : ℤ}
    (hqq' : q + s = q') (z : (moduleHom A D M N).X q) :
    (moduleHom A D (shiftModule s M) N).X q' :=
  moduleHomElementMk A D q'
    (fun x => ((moduleHomπ A D M N x.unop).f q z).leftShift s q' hqq')
    (moduleHomLeftShift_naturality A D s hqq' z)

lemma moduleHomLeftShiftElement_π (s : ℤ) {M N : RightModule A D} {q q' : ℤ}
    (hqq' : q + s = q') (z : (moduleHom A D M N).X q) (x : D) :
    (moduleHomπ A D (shiftModule s M) N x).f q' (moduleHomLeftShiftElement A D s hqq' z) =
      ((moduleHomπ A D M N x).f q z).leftShift s q' hqq' :=
  moduleHomElementMk_π A D q' _ _ x

lemma moduleHomLeftShiftElement_d (s : ℤ) {M N : RightModule A D} {q q' r r' : ℤ}
    (hqq' : q + s = q') (hrr' : r + s = r') (z : (moduleHom A D M N).X q) :
    (moduleHom A D (shiftModule s M) N).d q' r' (moduleHomLeftShiftElement A D s hqq' z) =
      s.negOnePow • moduleHomLeftShiftElement A D s hrr' ((moduleHom A D M N).d q r z) := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleHomLeftShiftElement_π]
  simp only [Units.smul_def, map_zsmul]
  rw [moduleHomLeftShiftElement_π, moduleHomElement_d_π, Cochain.δ_leftShift]
  rfl

lemma moduleHomLeftShiftElement_add (s : ℤ) {M N : RightModule A D} {q q' : ℤ}
    (hqq' : q + s = q') (z w : (moduleHom A D M N).X q) :
    moduleHomLeftShiftElement A D s hqq' (z + w) =
      moduleHomLeftShiftElement A D s hqq' z + moduleHomLeftShiftElement A D s hqq' w := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomLeftShiftElement_π, map_add, Cochain.leftShift_add, map_add,
    moduleHomLeftShiftElement_π, moduleHomLeftShiftElement_π]

lemma moduleHomLeftShiftElement_smul (s : ℤ) {M N : RightModule A D} {q q' : ℤ}
    (hqq' : q + s = q') (a : A) (z : (moduleHom A D M N).X q) :
    moduleHomLeftShiftElement A D s hqq' (a • z) =
      a • moduleHomLeftShiftElement A D s hqq' z := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomLeftShiftElement_π, map_smul, Cochain.leftShift_smul, map_smul,
    moduleHomLeftShiftElement_π]

lemma moduleHomLeftShiftElement_injective (s : ℤ) {M N : RightModule A D} {q q' : ℤ}
    (hqq' : q + s = q') : Function.Injective
      (moduleHomLeftShiftElement A D s (M := M) (N := N) hqq') := by
  intro z w h
  apply moduleHomElement_ext A D
  intro x
  have hx := congrArg ((moduleHomπ A D (shiftModule s M) N x).f q') h
  rw [moduleHomLeftShiftElement_π, moduleHomLeftShiftElement_π] at hx
  exact (Cochain.leftShiftLinearEquiv A (M.obj (op x)) (N.obj (op x)) q s q' hqq').injective hx


lemma moduleHomLeftShiftElement_zero (s : ℤ) {M N : RightModule A D} {q q' : ℤ}
    (hqq' : q + s = q') :
    moduleHomLeftShiftElement A D s (M := M) (N := N) hqq' 0 = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomLeftShiftElement_π, map_zero, Cochain.leftShift_zero, map_zero]

lemma moduleHomLeftShiftElement_neg (s : ℤ) {M N : RightModule A D} {q q' : ℤ}
    (hqq' : q + s = q') (z : (moduleHom A D M N).X q) :
    moduleHomLeftShiftElement A D s hqq' (-z) = -moduleHomLeftShiftElement A D s hqq' z := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomLeftShiftElement_π, map_neg, Cochain.leftShift_neg, map_neg,
    moduleHomLeftShiftElement_π]

lemma moduleHomLeftShiftElement_postcompose (s : ℤ) {M N P : ModuleCategory A D} {q q' : ℤ}
    (hqq' : q + s = q') (z : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).X q) (f : N ⟶ P) :
    moduleHomLeftShiftElement A D s hqq' ((eHomWhiskerLeft (Complex A) M f).f q z) =
      (eHomWhiskerLeft (Complex A) (moduleShiftObj A D s M) f).f q'
        (moduleHomLeftShiftElement A D s hqq' z) := by
  apply moduleHomElement_ext A D
    (M := shiftModule s (ForgetEnrichment.to (Complex A) M))
    (N := ForgetEnrichment.to (Complex A) P)
  intro x
  have h₁ := moduleHomWhiskerLeft_apply_π A D (T := M) f q z x
  have h₂ := moduleHomWhiskerLeft_apply_π A D (T := moduleShiftObj A D s M)
    f q' (moduleHomLeftShiftElement A D s hqq' z) x
  rw [moduleHomLeftShiftElement_π]
  have h₃ := congrArg (fun c => c.leftShift s q' hqq') h₁
  exact h₃.trans ((Cochain.leftShift_comp_zero_cochain _ s q' hqq' _).trans
    ((congrArg (fun c => c.comp (Cochain.ofHom ((moduleEvaluation A D x).map f)) (add_zero q'))
      (moduleHomLeftShiftElement_π A D s hqq' z x).symm).trans h₂.symm))

end SerrePositivity.DifferentialGraded
end

end LeftShiftElements

/-! ## ShiftUnitElements（旧 SerrePositivity/DifferentialGraded/Module/ShiftUnitElements.lean） -/

/-! # 加群shiftの互いに逆な斉次単位要素 -/

@[expose] public section ShiftUnitElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- Mathlib leftShiftの単位上の定数符号を保持した次数sの射影。 -/
def moduleShiftOutElement (s : ℤ) (M : RightModule A D) :
    (moduleHom A D (shiftModule s M) M).X s :=
  moduleHomLeftShiftElement A D s (zero_add s) (unitElement A M).val

lemma moduleShiftOutElement_π (s : ℤ) (M : RightModule A D) (x : D) :
    (moduleHomπ A D (shiftModule s M) M x).f s (moduleShiftOutElement A D s M) =
      (Cochain.ofHom (𝟙 (M.obj (op x)))).leftShift s s (zero_add s) := by
  rw [moduleShiftOutElement, moduleHomLeftShiftElement_π, yoneda_moduleUnit_π]

lemma moduleShiftOutElement_d (s : ℤ) (M : RightModule A D) :
    (moduleHom A D (shiftModule s M) M).d s (s + 1) (moduleShiftOutElement A D s M) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleShiftOutElement_π, map_zero,
    Cochain.δ_leftShift _ s s (s + 1) (zero_add s) 1 (by omega)]
  simp only [δ_ofHom, Cochain.leftShift_zero, smul_zero]

omit [Small.{u} D] in
lemma moduleShiftIn_naturality (s : ℤ) (M : RightModule A D)
    (x y : Dᵒᵖ) (p : ℤ) (f : GradedHom A x y p) :
    ((M.map x y).f p f).comp
        ((Cochain.ofHom (𝟙 (M.obj y))).rightShift s (-s) (neg_add_cancel s)) (by omega) =
      ((-s) * p).negOnePow •
        (((Cochain.ofHom (𝟙 (M.obj x))).rightShift s (-s) (neg_add_cancel s)).comp
          (((shiftModule s M).map x y).f p f) rfl) := by
  apply Cochain.ext
  intro i j hij
  rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega), Cochain.units_smul_v,
    Cochain.comp_v _ _ _ i (i - s) j (by omega) (by omega), shiftModule_map_v,
    Cochain.rightShift_v _ s (-s) (neg_add_cancel s) (i + p) j (by omega) (i + p) (add_zero _),
    Cochain.rightShift_v _ s (-s) (neg_add_cancel s) i (i - s) (by omega) i (add_zero _)]
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f,
    CochainComplex.shiftFunctorObjXIso, Category.id_comp,
    Linear.comp_units_smul, smul_smul, ← Int.negOnePow_add]
  have h : (-s) * p + s * p = 0 := by ring
  rw [h, Int.negOnePow_zero, one_smul]
  rw [Cochain.v_comp_XIsoOfEq_inv, homogeneous_XIsoOfEq_inv_comp]

/-- 次数−sの包含。射影の定数符号を掛け、通常順の両合成を単位にする。 -/
def moduleShiftInElement (s : ℤ) (M : RightModule A D) :
    (moduleHom A D M (shiftModule s M)).X (-s) :=
  (s * s + s * (s - 1) / 2).negOnePow •
    moduleHomElementMk A D (-s)
      (fun x => (Cochain.ofHom (𝟙 (M.obj x))).rightShift s (-s) (neg_add_cancel s))
      (moduleShiftIn_naturality A D s M)

lemma moduleShiftInElement_π (s : ℤ) (M : RightModule A D) (x : D) :
    (moduleHomπ A D M (shiftModule s M) x).f (-s) (moduleShiftInElement A D s M) =
      (s * s + s * (s - 1) / 2).negOnePow •
        (Cochain.ofHom (𝟙 (M.obj (op x)))).rightShift s (-s) (neg_add_cancel s) := by
  simp only [moduleShiftInElement, Units.smul_def, map_zsmul, moduleHomElementMk_π]

end SerrePositivity.DifferentialGraded
end

end ShiftUnitElements

/-! ## ShiftUnitRelations（旧 SerrePositivity/DifferentialGraded/Module/ShiftUnitRelations.lean） -/

/-! # shiftの包含・射影の通常順合成 -/

@[expose] public section ShiftUnitRelations
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleShiftOutIn (s : ℤ) (M : RightModule A D) :
    compose A (moduleShiftInElement A D s M) (moduleShiftOutElement A D s M)
        (add_neg_cancel s) = (unitElement A (shiftModule s M)).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, moduleShiftOutElement_π, moduleShiftInElement_π, yoneda_moduleUnit_π]
  apply Cochain.ext₀
  intro i
  rw [Cochain.comp_v _ _ _ i (i + s) i rfl (by omega), Cochain.units_smul_v,
    Cochain.leftShift_v _ s s (zero_add s) i (i + s) rfl (i + s) (add_zero _),
    Cochain.rightShift_v _ s (-s) (neg_add_cancel s) (i + s) i (by omega) (i + s) (add_zero _)]
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Iso.refl_inv, Category.comp_id,
    Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul]
  rfl

lemma moduleShiftInOut (s : ℤ) (M : RightModule A D) :
    compose A (moduleShiftOutElement A D s M) (moduleShiftInElement A D s M)
        (neg_add_cancel s) = (unitElement A M).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, moduleShiftInElement_π, moduleShiftOutElement_π, yoneda_moduleUnit_π]
  apply Cochain.ext₀
  intro i
  rw [Cochain.comp_v _ _ _ i (i - s) i (by omega) (by omega), Cochain.units_smul_v,
    Cochain.rightShift_v _ s (-s) (neg_add_cancel s) i (i - s) (by omega) i (add_zero _),
    Cochain.leftShift_v _ s s (zero_add s) (i - s) i (by omega) i (add_zero _)]
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f,
    CochainComplex.shiftFunctorObjXIso, Category.id_comp, Category.comp_id,
    Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul]
  exact (XIsoOfEq (M.obj (op x)) (show i - s + s = i by omega)).inv_hom_id

end SerrePositivity.DifferentialGraded
end

end ShiftUnitRelations

/-! ## ShiftUnitDifferential（旧 SerrePositivity/DifferentialGraded/Module/ShiftUnitDifferential.lean） -/

/-! # shift包含の閉性 -/

@[expose] public section ShiftUnitDifferential
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleShiftInElement_d (s : ℤ) (M : RightModule A D) :
    (moduleHom A D M (shiftModule s M)).d (-s) (-s + 1) (moduleShiftInElement A D s M) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleShiftInElement_π, map_zero, δ_units_smul,
    Cochain.δ_rightShift _ s (-s) (-s + 1) (neg_add_cancel s) 1 (by omega)]
  simp only [δ_ofHom, Cochain.rightShift_zero, smul_zero]

end SerrePositivity.DifferentialGraded
end

end ShiftUnitDifferential

/-! ## ShiftBlocks（旧 SerrePositivity/DifferentialGraded/Module/ShiftBlocks.lean） -/

/-!
概要：異なるシフト間の斉次 Hom を、元の斉次 Hom から構成する。
方針：互いに逆な shift の斉次単位で前後から合成する。
規約：元の全次数 Hom と二つの shift を保持し、次数の等式を明示する。
使われ方：coherent bar 微分の単体ごとのブロック。
-/

@[expose] public section ShiftBlocks
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- シフト包含・射影による、元の斉次 Hom の同じブロック。 -/
def moduleHomShiftBlock (s t : ℤ) {M N : RightModule R D} {q k : ℤ}
    (f : (moduleHom R D M N).X q) (hk : s + q - t = k) :
    (moduleHom R D (shiftModule s M) (shiftModule t N)).X k :=
  compose R (x := shiftModule s M) (y := N) (z := shiftModule t N)
    (moduleShiftInElement R D t N)
    (compose R (x := shiftModule s M) (y := M) (z := N)
      f (moduleShiftOutElement R D s M) rfl) (by omega)

lemma moduleHomShiftBlock_π (s t : ℤ) {M N : RightModule R D} {q k : ℤ}
    (f : (moduleHom R D M N).X q) (hk : s + q - t = k) (x : D) :
    (moduleHomπ R D (shiftModule s M) (shiftModule t N) x).f k
      (moduleHomShiftBlock R D s t f hk) =
    (((moduleHomπ R D (shiftModule s M) M x).f s (moduleShiftOutElement R D s M)).comp
      ((moduleHomπ R D M N x).f q f) rfl).comp
      ((moduleHomπ R D N (shiftModule t N) x).f (-t) (moduleShiftInElement R D t N))
      (by omega) := by
  unfold moduleHomShiftBlock
  rw [moduleHomCompose_π, moduleHomCompose_π]

lemma moduleHomShiftBlock_d (s t : ℤ) {M N : RightModule R D} {q k : ℤ}
    (f : (moduleHom R D M N).X q) (hk : s + q - t = k) :
    (moduleHom R D (shiftModule s M) (shiftModule t N)).d k (k + 1)
      (moduleHomShiftBlock R D s t f hk) =
      (-t).negOnePow • moduleHomShiftBlock R D s t
        ((moduleHom R D M N).d q (q + 1) f) (by omega : s + (q + 1) - t = k + 1) := by
  have hi : differential R (x := N) (y := shiftModule t N)
      (moduleShiftInElement R D t N) = 0 := moduleShiftInElement_d R D t N
  have ho : differential R (x := shiftModule s M) (y := M)
      (moduleShiftOutElement R D s M) = 0 := moduleShiftOutElement_d R D s M
  subst k
  unfold moduleHomShiftBlock
  change differential R (x := shiftModule s M) (y := shiftModule t N) _ = _
  rw [differential_compose, differential_compose, hi, ho]
  simp only [compose, forward, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
    map_zero, smul_zero, zero_add, add_zero]
  let φ (a : {a : ℤ // s + (q + 1) = a}) :
      (moduleHom R D (shiftModule s M) (shiftModule t N)).X (s + q - t + 1) :=
    (-t).negOnePow • compose R (x := shiftModule s M) (y := N) (z := shiftModule t N)
      (moduleShiftInElement R D t N)
      (compose R (x := shiftModule s M) (y := M) (z := N)
        ((moduleHom R D M N).d q (q + 1) f) (moduleShiftOutElement R D s M) a.property)
      (by have := a.property; omega)
  have he : (⟨s + q + 1, by omega⟩ : {a : ℤ // s + (q + 1) = a}) =
      ⟨s + (q + 1), rfl⟩ := Subtype.ext (by change s + q + 1 = s + (q + 1); omega)
  have hφ := congrArg φ he
  dsimp only [φ, compose, forward, differential] at hφ
  exact hφ

end SerrePositivity.DifferentialGraded
end

end ShiftBlocks

/-! ## ShiftBlockLinear（旧 SerrePositivity/DifferentialGraded/Module/ShiftBlockLinear.lean） -/

/-!
概要：シフト間の斉次ブロック構成は、元の Hom 加群の線形写像である。
方針：元の評価ごとの cochain 合成へ戻し、中間係数の加法性と線形性を使う。
規約：次数と両端の shift を明示し、有限和と符号スカラーを同じ写像で扱う。
使われ方：HA 微分の有限和を bar の shift ブロックへ送る。
-/

@[expose] public section ShiftBlockLinear
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R]

/-- 概要：二つの固定 cochain の間の合成を線形写像として扱う。
方針：cochain 合成の両線形性を使う。
規約：三つの次数の和を明示する。使われ方：shift ブロックの係数の線形性。 -/
def cochainSandwichLinear {K M N L : Complex R} {s t : ℤ}
    (A : Cochain K M s) (B : Cochain N L t) (q k : ℤ) (hk : s + q + t = k) :
    Cochain M N q →ₗ[R] Cochain K L k where
  toFun f := (A.comp f rfl).comp B hk
  map_add' f g := by rw [Cochain.comp_add, Cochain.add_comp]
  map_smul' a f := by rw [Cochain.comp_smul, Cochain.smul_comp]; rfl

variable (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：シフト間のブロックを作る線形写像。
方針：両側の斉次単位との合成を評価する。
規約：全次数の等式を明示する。使われ方：bar 係数の有限和と微分。 -/
def moduleHomShiftBlockLinear (s t : ℤ) (M N : RightModule R D) (q k : ℤ)
    (hk : s + q - t = k) :
    (moduleHom R D M N).X q →ₗ[R]
      (moduleHom R D (shiftModule s M) (shiftModule t N)).X k where
  toFun f := moduleHomShiftBlock R D s t f hk
  map_add' f g := by
    apply moduleHomElement_ext R D (M := shiftModule s M) (N := shiftModule t N)
    intro x
    simp only [map_add, moduleHomShiftBlock_π]
    exact (cochainSandwichLinear R
      ((moduleHomπ R D (shiftModule s M) M x).f s (moduleShiftOutElement R D s M))
      ((moduleHomπ R D N (shiftModule t N) x).f (-t) (moduleShiftInElement R D t N))
      q k (by omega)).map_add _ _
  map_smul' a f := by
    apply moduleHomElement_ext R D (M := shiftModule s M) (N := shiftModule t N)
    intro x
    simp only [map_smul, moduleHomShiftBlock_π, RingHom.id_apply]
    exact (cochainSandwichLinear R
      ((moduleHomπ R D (shiftModule s M) M x).f s (moduleShiftOutElement R D s M))
      ((moduleHomπ R D N (shiftModule t N) x).f (-t) (moduleShiftInElement R D t N))
      q k (by omega)).map_smul a _

lemma moduleHomShiftBlock_zero (s t : ℤ) (M N : RightModule R D) (q k : ℤ)
    (hk : s + q - t = k) :
    moduleHomShiftBlock R D s t (0 : (moduleHom R D M N).X q) hk = 0 :=
  (moduleHomShiftBlockLinear R D s t M N q k hk).map_zero

lemma moduleHomShiftBlock_unit_d (s t : ℤ) (M : RightModule R D) (k : ℤ)
    (hk : s + 0 - t = k) :
    (moduleHom R D (shiftModule s M) (shiftModule t M)).d k (k + 1)
      (moduleHomShiftBlock R D s t (unitElement R M).val hk) = 0 := by
  rw [moduleHomShiftBlock_d R D]
  have hu : (moduleHom R D M M).d 0 1 (unitElement R M).val = 0 :=
    differential_unit R M
  let L := moduleHomShiftBlockLinear R D s t M M 1 (k + 1) (by omega)
  have hb := (congrArg L hu).trans L.map_zero
  exact (congrArg (fun z => (-t).negOnePow • z) hb).trans (smul_zero _)

end SerrePositivity.DifferentialGraded
end

end ShiftBlockLinear

/-! ## ShiftBlockComposition（旧 SerrePositivity/DifferentialGraded/Module/ShiftBlockComposition.lean） -/

/-!
概要：シフト間の斉次 Hom ブロックの合成は、元の斉次 Hom の合成と厳密に一致する。
方針：評価ごとの六項合成で、中間の shift 包含・射影の対を消去する。
規約：全次数と三つの shift を保ち、閉零射や h 圏へ制限しない。
使われ方：coherent bar の二段 prefix に現れる二乗項。
-/

@[expose] public section ShiftBlockComposition
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma moduleHomShiftBlock_comp (s t r : ℤ) {M N P : RightModule R D} {p q a b c : ℤ}
    (f : (moduleHom R D M N).X p) (g : (moduleHom R D N P).X q)
    (ha : s + p - t = a) (hb : t + q - r = b) (hc : a + b = c) :
    compose R (x := shiftModule s M) (y := shiftModule t N) (z := shiftModule r P)
      (moduleHomShiftBlock R D t r g hb) (moduleHomShiftBlock R D s t f ha) hc =
      moduleHomShiftBlock R D s r (compose R (x := M) (y := N) (z := P) g f rfl)
        (by omega : s + (p + q) - r = c) := by
  apply moduleHomElement_ext R D (M := shiftModule s M) (N := shiftModule r P)
  intro x
  rw [moduleHomCompose_π R D, moduleHomShiftBlock_π R D,
    moduleHomShiftBlock_π R D, moduleHomShiftBlock_π R D, moduleHomCompose_π R D]
  have hu := congrArg ((moduleHomπ R D N N x).f 0) (moduleShiftInOut R D t N)
  rw [moduleHomCompose_π R D, yoneda_moduleUnit_π] at hu
  exact cochainSixfold_cancel _ _ _ _ _ _ hu ha hb hc

end SerrePositivity.DifferentialGraded
end

end ShiftBlockComposition

/-! ## ResolutionSequence（旧 SerrePositivity/DifferentialGraded/Module/ResolutionSequence.lean） -/

/-! # kernelのcycleを順に消す可算cell列

自由disk被覆から始め、各段階で前段のkernelの全cycleを消す。
このファイルの余極限は解像度の候補であり、準同型性とsemifree性は別途証明する。
-/

@[expose] public section ResolutionSequence
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleResolutionStage (M : ModuleCategory A D) : ℕ → Over M
  | 0 => Over.mk (moduleDiskCoverπ A D M)
  | n + 1 => Over.mk (moduleKernelCellStepπ A D (moduleResolutionStage M n).hom)

def moduleResolutionTransition (M : ModuleCategory A D) (n : ℕ) :
    moduleResolutionStage A D M n ⟶ moduleResolutionStage A D M (n + 1) :=
  Over.homMk (moduleKernelCellStepι A D (moduleResolutionStage A D M n).hom)
    (moduleKernelCellStep_fac A D _)

lemma moduleResolutionStage_degreewiseSurjective (M : ModuleCategory A D) (n : ℕ) :
    moduleDegreewiseSurjective A D (moduleResolutionStage A D M n).hom := by
  induction n with
  | zero => exact moduleDiskCoverπ_degreewiseSurjective A D M
  | succ n hn => exact moduleKernelCellStepπ_degreewiseSurjective A D _ hn

def moduleResolutionOverDiagram (M : ModuleCategory A D) : ℕ ⥤ Over M :=
  Functor.ofSequence (moduleResolutionTransition A D M)

def moduleResolutionDiagram (M : ModuleCategory A D) : ℕ ⥤ ModuleCategory A D :=
  moduleResolutionOverDiagram A D M ⋙ Over.forget M

def moduleResolutionCocone (M : ModuleCategory A D) : Cocone (moduleResolutionDiagram A D M) where
  pt := M
  ι :=
    { app n := (moduleResolutionStage A D M n).hom
      naturality i j f := by
        change ((moduleResolutionOverDiagram A D M).map f).left ≫
          (moduleResolutionStage A D M j).hom = (moduleResolutionStage A D M i).hom ≫ 𝟙 M
        rw [Category.comp_id]
        exact Over.w _ }

/-- 可算cell列の余極限。準同型・semifree性の証明前の候補。 -/
def moduleResolutionCandidate (M : ModuleCategory A D) : ModuleCategory A D :=
  colimit (moduleResolutionDiagram A D M)

def moduleResolutionCandidateπ (M : ModuleCategory A D) : moduleResolutionCandidate A D M ⟶ M :=
  colimit.desc _ (moduleResolutionCocone A D M)

def moduleResolutionCandidateι (M : ModuleCategory A D) (n : ℕ) :
    (moduleResolutionStage A D M n).left ⟶ moduleResolutionCandidate A D M :=
  colimit.ι (moduleResolutionDiagram A D M) n

@[reassoc] lemma moduleResolutionCandidateι_π (M : ModuleCategory A D) (n : ℕ) :
    moduleResolutionCandidateι A D M n ≫ moduleResolutionCandidateπ A D M =
      (moduleResolutionStage A D M n).hom :=
  colimit.ι_desc (moduleResolutionCocone A D M) n

@[reassoc] lemma moduleResolutionCandidateι_succ (M : ModuleCategory A D) (n : ℕ) :
    (moduleResolutionTransition A D M n).left ≫ moduleResolutionCandidateι A D M (n + 1) =
      moduleResolutionCandidateι A D M n := by
  have h := colimit.w (moduleResolutionDiagram A D M) (homOfLE (Nat.le_succ n))
  have hm : (moduleResolutionDiagram A D M).map (homOfLE (Nat.le_succ n)) =
      (moduleResolutionTransition A D M n).left := by
    simp only [moduleResolutionDiagram, Functor.comp_map, Over.forget_map,
      moduleResolutionOverDiagram, Functor.ofSequence_map_homOfLE_succ]
  change (moduleResolutionDiagram A D M).map (homOfLE (Nat.le_succ n)) ≫
    moduleResolutionCandidateι A D M (n + 1) = moduleResolutionCandidateι A D M n at h
  rw [hm] at h
  exact h

lemma moduleResolutionCandidateπ_degreewiseSurjective (M : ModuleCategory A D) :
    moduleDegreewiseSurjective A D (moduleResolutionCandidateπ A D M) := by
  intro x n y
  obtain ⟨t, ht⟩ := moduleResolutionStage_degreewiseSurjective A D M 0 x n y
  refine ⟨((moduleEvaluation A D x).map (colimit.ι (moduleResolutionDiagram A D M) 0)).f n t, ?_⟩
  have h := congrArg (fun k => ((moduleEvaluation A D x).map k).f n t)
    (colimit.ι_desc (moduleResolutionCocone A D M) 0)
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] at h
  exact h.trans ht

/-- 有限段のkernel内のcycleは、最終候補でkernel内の境界になる。 -/
lemma moduleResolutionCandidate_killsStage (M : ModuleCategory A D) (k : ℕ) (x : D) (n : ℤ)
    (z : complexCycles A ((moduleEvaluation A D x).obj
      (moduleResolutionStage A D M k).left) (n + 1))
    (hz : ((moduleEvaluation A D x).map (moduleResolutionStage A D M k).hom).f (n + 1) z.val = 0) :
    ∃ t : ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)).X n,
      ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)).d n (n + 1) t =
        ((moduleEvaluation A D x).map (moduleResolutionCandidateι A D M k)).f (n + 1) z.val ∧
      ((moduleEvaluation A D x).map (moduleResolutionCandidateπ A D M)).f n t = 0 := by
  obtain ⟨t, ht, hq⟩ := moduleKernelCellStep_killsInKernel A D
    (moduleResolutionStage A D M k).hom x n z hz
  let i := (moduleEvaluation A D x).map (moduleResolutionCandidateι A D M (k + 1))
  refine ⟨i.f n t, ?_, ?_⟩
  · have h := congrArg (fun f => ((moduleEvaluation A D x).map f).f (n + 1) z.val)
      (moduleResolutionCandidateι_succ A D M k)
    rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] at h
    have hd := congrArg (fun f => f t) (i.comm n (n + 1))
    exact hd.trans ((congrArg (i.f (n + 1)) ht).trans h)
  · have h := congrArg (fun f => ((moduleEvaluation A D x).map f).f n t)
      (moduleResolutionCandidateι_π A D M (k + 1))
    rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] at h
    exact h.trans hq

end SerrePositivity.DifferentialGraded
end

end ResolutionSequence

/-! ## ResolutionQuasiIso（旧 SerrePositivity/DifferentialGraded/Module/ResolutionQuasiIso.lean） -/

/-! # 可算cell候補からの射の準同型性

全kernel cycleを有限段へ持ち上げ、一段階後で消す。semifree filtrationは別途構成する。
-/

@[expose] public section ResolutionQuasiIso
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleResolutionCandidate_cycle_rep (M : ModuleCategory A D) (x : D) (n : ℤ)
    (z : complexCycles A ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)) n) :
    ∃ (k : ℕ) (t : complexCycles A ((moduleEvaluation A D x).obj
      (moduleResolutionStage A D M k).left) n),
      ((moduleEvaluation A D x).map (moduleResolutionCandidateι A D M k)).f n t.val = z.val := by
  exact complexSequentialColimit_cycle_rep A
    (moduleResolutionDiagram A D M ⋙ moduleEvaluation A D x)
    ((moduleEvaluation A D x).mapCocone (colimit.cocone (moduleResolutionDiagram A D M)))
    (isColimitOfPreserves (moduleEvaluation A D x) (colimit.isColimit _)) n z

lemma moduleResolutionCandidate_kernelCycle_boundary (M : ModuleCategory A D) (x : D) (n : ℤ)
    (z : complexCycles A ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)) (n + 1))
    (hz : ((moduleEvaluation A D x).map (moduleResolutionCandidateπ A D M)).f (n + 1) z.val = 0) :
    ∃ t : ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)).X n,
      ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)).d n (n + 1) t = z.val ∧
      ((moduleEvaluation A D x).map (moduleResolutionCandidateπ A D M)).f n t = 0 := by
  obtain ⟨k, c, hc⟩ := moduleResolutionCandidate_cycle_rep A D M x (n + 1) z
  have hkc : ((moduleEvaluation A D x).map (moduleResolutionStage A D M k).hom).f
      (n + 1) c.val = 0 := by
    have h := congrArg (fun f => ((moduleEvaluation A D x).map f).f (n + 1) c.val)
      (moduleResolutionCandidateι_π A D M k)
    rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] at h
    exact h.symm.trans ((congrArg
      (((moduleEvaluation A D x).map (moduleResolutionCandidateπ A D M)).f (n + 1)) hc).trans hz)
  obtain ⟨t, ht, hq⟩ := moduleResolutionCandidate_killsStage A D M k x n c hkc
  exact ⟨t, ht.trans hc, hq⟩

lemma moduleResolutionCandidate_boundaryLift (M : ModuleCategory A D) (x : D) (n : ℤ) :
    moduleBoundaryLiftAt A D x n (moduleResolutionCandidateπ A D M) := by
  intro z y hzy
  let K := (moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)
  let L := (moduleEvaluation A D x).obj M
  let f := (moduleEvaluation A D x).map (moduleResolutionCandidateπ A D M)
  obtain ⟨t, ht⟩ := moduleResolutionCandidateπ_degreewiseSurjective A D M x n y
  have hd : K.d (n + 1) (n + 1 + 1) (K.d n (n + 1) t) = 0 :=
    congrArg (fun a => a t) (K.d_comp_d n (n + 1) (n + 1 + 1))
  let c : complexCycles A K (n + 1) := ⟨z.val - K.d n (n + 1) t, by
    change K.d (n + 1) (n + 1 + 1) (z.val - K.d n (n + 1) t) = 0
    rw [map_sub, z.property, hd, sub_self]⟩
  have hc : f.f (n + 1) c.val = 0 := by
    have h := congrArg (fun a => a t) (f.comm n (n + 1))
    change L.d n (n + 1) (f.f n t) = f.f (n + 1) (K.d n (n + 1) t) at h
    change f.f (n + 1) (z.val - K.d n (n + 1) t) = 0
    rw [map_sub, ← h, ht, hzy, sub_self]
  obtain ⟨w, hw, hq⟩ := moduleResolutionCandidate_kernelCycle_boundary A D M x n c hc
  refine ⟨t + w, ?_, ?_⟩
  · change K.d n (n + 1) (t + w) = z.val
    rw [map_add, hw]
    change K.d n (n + 1) t + (z.val - K.d n (n + 1) t) = z.val
    exact (add_comm (K.d n (n + 1) t) (z.val - K.d n (n + 1) t)).trans
      (sub_add_cancel _ _)
  · change f.f n (t + w) = y
    rw [map_add, ht, hq, add_zero]

/-- 可算cell付加の余極限から元の加群への射は指定objectwise quasiIso。 -/
lemma moduleResolutionCandidateπ_quasiIso (M : ModuleCategory A D) :
    moduleQuasiIso A D (moduleResolutionCandidateπ A D M) :=
  moduleQuasiIso_of_boundary_lifting A D _ (moduleResolutionCandidate_boundaryLift A D M)

end SerrePositivity.DifferentialGraded
end

end ResolutionQuasiIso

/-! ## ResolutionGradedSteps（旧 SerrePositivity/DifferentialGraded/Module/ResolutionGradedSteps.lean） -/

/-! # 可算cell列の各付加の分裂と商

初期disk段のsphereへの分解と自由な商の同定は後続に残す。
-/

@[expose] public section ResolutionGradedSteps
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- kernel cell付加の商への標準射。 -/
def moduleKernelCellStepQuotient {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleKernelCellStep A D f ⟶ (moduleKernelCellSource A D f)⟦(1 : ℤ)⟧ :=
  moduleConeConnecting A D (moduleKernelCellMap A D f)

def moduleKernelCellStepGradedSplit {M N : ModuleCategory A D} (f : M ⟶ N) :
    ModuleGradedSplit A D (moduleKernelCellStepι A D f) (moduleKernelCellStepQuotient A D f) :=
  moduleConeGradedSplit A D (moduleKernelCellMap A D f)

lemma moduleKernelCellStepι_mono {M N : ModuleCategory A D} (f : M ⟶ N) :
    Mono (moduleKernelCellStepι A D f) := (moduleKernelCellStepGradedSplit A D f).mono

def moduleKernelCellStepCokernel {M N : ModuleCategory A D} (f : M ⟶ N) :
    IsColimit (CokernelCofork.ofπ (moduleKernelCellStepQuotient A D f)
      (moduleKernelCellStepGradedSplit A D f).inclusion_projection) :=
  moduleGradedSplitCokernel A D (moduleKernelCellStepGradedSplit A D f)

lemma moduleResolutionTransition_mono (M : ModuleCategory A D) (k : ℕ) :
    Mono (moduleResolutionTransition A D M k).left :=
  moduleKernelCellStepι_mono A D (moduleResolutionStage A D M k).hom

/-- 有限段から後の有限段への射はmono。 -/
lemma moduleResolutionDiagram_map_mono (M : ModuleCategory A D) (i j : ℕ) (h : i ≤ j) :
    Mono ((moduleResolutionDiagram A D M).map (homOfLE h)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simpa using (inferInstance : Mono (𝟙 ((moduleResolutionDiagram A D M).obj i)))
  | succ k hk =>
    have he : (moduleResolutionDiagram A D M).map (homOfLE h) =
        (moduleResolutionDiagram A D M).map (homOfLE (Nat.le_add_right i k)) ≫
          (moduleResolutionTransition A D M (i + k)).left := by
      rw [show homOfLE h = homOfLE (Nat.le_add_right i k) ≫ homOfLE (Nat.le_succ (i + k)) from rfl,
        CategoryTheory.Functor.map_comp]
      congr 1
      simp only [moduleResolutionDiagram, Functor.comp_map, Over.forget_map,
        moduleResolutionOverDiagram, Functor.ofSequence_map_homOfLE_succ]
    let : Mono ((moduleResolutionDiagram A D M).map (homOfLE (Nat.le_add_right i k))) := hk _
    let : Mono (moduleResolutionTransition A D M (i + k)).left :=
      moduleResolutionTransition_mono A D M _
    rw [he]
    infer_instance

lemma moduleResolutionDiagram_map_degreewiseMono (M : ModuleCategory A D)
    (x : D) (n : ℤ) (i j : ℕ) (h : i ≤ j) :
    Mono (((moduleEvaluation A D x).map
      ((moduleResolutionDiagram A D M).map (homOfLE h))).f n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simp only [homOfLE_refl, CategoryTheory.Functor.map_id,
      HomologicalComplex.id_f]; infer_instance
  | succ k hk =>
    have he : (moduleResolutionDiagram A D M).map (homOfLE h) =
        (moduleResolutionDiagram A D M).map (homOfLE (Nat.le_add_right i k)) ≫
          (moduleResolutionTransition A D M (i + k)).left := by
      rw [show homOfLE h = homOfLE (Nat.le_add_right i k) ≫ homOfLE (Nat.le_succ (i + k)) from rfl,
        CategoryTheory.Functor.map_comp]
      congr 1
      simp only [moduleResolutionDiagram, Functor.comp_map, Over.forget_map,
        moduleResolutionOverDiagram, Functor.ofSequence_map_homOfLE_succ]
    let : Mono (((moduleEvaluation A D x).map
      ((moduleResolutionDiagram A D M).map (homOfLE (Nat.le_add_right i k)))).f n) := hk _
    let : Mono (((moduleEvaluation A D x).map
      (moduleResolutionTransition A D M (i + k)).left).f n) :=
      (moduleKernelCellStepGradedSplit A D
        (moduleResolutionStage A D M (i + k)).hom).degreewiseMono x n
    rw [he, CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f]
    infer_instance

/-- 各有限段の余極限への包含は全評価次数でmono。 -/
lemma moduleResolutionCandidateι_degreewiseMono (M : ModuleCategory A D)
    (k : ℕ) (x : D) (n : ℤ) :
    Mono (((moduleEvaluation A D x).map (moduleResolutionCandidateι A D M k)).f n) := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n
  let F := (moduleResolutionDiagram A D M ⋙ moduleEvaluation A D x) ⋙ ev
  let s := ev.mapCocone ((moduleEvaluation A D x).mapCocone
    (colimit.cocone (moduleResolutionDiagram A D M)))
  have hs : IsColimit s := isColimitOfPreserves ev
    (isColimitOfPreserves (moduleEvaluation A D x) (colimit.isColimit _))
  apply (ModuleCat.mono_iff_injective _).2
  intro a b hab
  obtain ⟨j, f, g, hj⟩ := Concrete.isColimit_exists_of_rep_eq F hs a b hab
  have hfg : g = f := Subsingleton.elim _ _
  rw [hfg] at hj
  have hm : Mono (F.map f) := moduleResolutionDiagram_map_degreewiseMono A D M x n k j (leOfHom f)
  exact (ModuleCat.mono_iff_injective _).1 hm hj

/-- 各有限段は主dg加群圏でも余極限候補へ埋め込まれる。 -/
lemma moduleResolutionCandidateι_mono (M : ModuleCategory A D) (k : ℕ) :
    Mono (moduleResolutionCandidateι A D M k) where
  right_cancellation a b h := by
    apply moduleMorphism_ext
    intro x
    apply HomologicalComplex.Hom.ext
    funext n
    let : Mono (((moduleEvaluation A D x).map (moduleResolutionCandidateι A D M k)).f n) :=
      moduleResolutionCandidateι_degreewiseMono A D M k x n
    apply (cancel_mono (((moduleEvaluation A D x).map (moduleResolutionCandidateι A D M k)).f n)).1
    have he := congrArg (fun f => ((moduleEvaluation A D x).map f).f n) h
    simpa only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] using he

/-- 各評価次数の全要素は有限段の像に属する。 -/
lemma moduleResolutionCandidate_element_rep (M : ModuleCategory A D) (x : D) (n : ℤ)
    (z : ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)).X n) :
    ∃ (k : ℕ) (t : ((moduleEvaluation A D x).obj (moduleResolutionStage A D M k).left).X n),
      ((moduleEvaluation A D x).map (moduleResolutionCandidateι A D M k)).f n t = z := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n
  exact Concrete.isColimit_exists_rep
    ((moduleResolutionDiagram A D M ⋙ moduleEvaluation A D x) ⋙ ev)
    (isColimitOfPreserves ev
      (isColimitOfPreserves (moduleEvaluation A D x) (colimit.isColimit _))) z

end SerrePositivity.DifferentialGraded
end

end ResolutionGradedSteps

/-! ## ResolutionFreeQuotients（旧 SerrePositivity/DifferentialGraded/Module/ResolutionFreeQuotients.lean） -/

/-! # 可算cell付加の商は自由sphereの余積

既存の真の商の対象を、shiftを含まない自由sphere族に同定する。
-/

@[expose] public section ResolutionFreeQuotients
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 次数n+1のkernel cycleを消す付加の商は次数nの自由sphere。 -/
def moduleKernelCellQuotientFamily {M N : ModuleCategory A D} (f : M ⟶ N) :
    ModuleKernelCellIndex A D f → ModuleCategory A D :=
  fun t => freeSphere A D t.1 t.2.1

/-- 真の商対象 `(∐ freeSphere(n+1))[1]` の自由sphere余積による表示。 -/
def moduleKernelCellQuotientFreeIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleKernelCellSource A D f)⟦(1 : ℤ)⟧ ≅ ∐ moduleKernelCellQuotientFamily A D f :=
  moduleShiftCoproductIso A D (moduleKernelCellFamily A D f) 1 ≪≫
    Limits.Sigma.mapIso (fun t : ModuleKernelCellIndex A D f =>
      freeSphereShiftIso A D t.1 (t.2.1 + 1) 1 ≪≫
        eqToIso (congrArg (freeSphere A D t.1) (by omega : t.2.1 + 1 - 1 = t.2.1)))

end SerrePositivity.DifferentialGraded
end

end ResolutionFreeQuotients

/-! ## Resolution（旧 SerrePositivity/DifferentialGraded/Module/Semifree/Resolution.lean） -/

/-! # 任意dg加群のsemifree解像度

初期sphere段を既存の可算cell列の前に加え、その余極限が既存候補であることを証明する。
-/

@[expose] public section Resolution
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleSemifreeResolutionStage (M : ModuleCategory A D) : ℕ → ModuleCategory A D
  | 0 => ∐ moduleDiskCoverUpperFamily A D M
  | k + 1 => (moduleResolutionStage A D M k).left

def moduleSemifreeResolutionTransition (M : ModuleCategory A D) (k : ℕ) :
    moduleSemifreeResolutionStage A D M k ⟶ moduleSemifreeResolutionStage A D M (k + 1) :=
  match k with
  | 0 => moduleDiskCoverBoundary A D M
  | k + 1 => (moduleResolutionTransition A D M k).left

def moduleSemifreeResolutionDiagram (M : ModuleCategory A D) : ℕ ⥤ ModuleCategory A D :=
  Functor.ofSequence (moduleSemifreeResolutionTransition A D M)

/-- refined列へのcoconeを、既存列のtail coconeへ制限する。 -/
def moduleSemifreeResolutionTailCocone (M : ModuleCategory A D)
    (c : Cocone (moduleSemifreeResolutionDiagram A D M)) :
    Cocone (moduleResolutionDiagram A D M) where
  pt := c.pt
  ι := NatTrans.ofSequence (fun k => c.ι.app (k + 1)) (by
    intro k
    have h := c.w (homOfLE (Nat.le_succ (k + 1)))
    simp only [moduleSemifreeResolutionDiagram, Functor.ofSequence_map_homOfLE_succ] at h
    change (moduleResolutionTransition A D M k).left ≫ c.ι.app (k + 1 + 1) =
      c.ι.app (k + 1) at h
    change (moduleResolutionDiagram A D M).map (homOfLE (Nat.le_succ k)) ≫
      c.ι.app (k + 1 + 1) = c.ι.app (k + 1) ≫ 𝟙 _
    simpa only [moduleResolutionDiagram, Functor.comp_map, Over.forget_map,
      moduleResolutionOverDiagram, Functor.ofSequence_map_homOfLE_succ, Category.comp_id] using h)

def moduleSemifreeResolutionCocone (M : ModuleCategory A D) :
    Cocone (moduleSemifreeResolutionDiagram A D M) where
  pt := moduleResolutionCandidate A D M
  ι := NatTrans.ofSequence
    (fun k => match k with
      | 0 => moduleDiskCoverBoundary A D M ≫ moduleResolutionCandidateι A D M 0
      | k + 1 => moduleResolutionCandidateι A D M k) (by
        intro k
        cases k with
        | zero =>
          simp only [moduleSemifreeResolutionDiagram,
            Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
          exact (Category.comp_id _).symm
        | succ k =>
          simp only [moduleSemifreeResolutionDiagram,
            Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
          exact (moduleResolutionCandidateι_succ A D M k).trans (Category.comp_id _).symm)

/-- 初期段を一段追加しても、既存の余極限候補が余極限である。 -/
def moduleSemifreeResolutionIsColimit (M : ModuleCategory A D) :
    IsColimit (moduleSemifreeResolutionCocone A D M) where
  desc c := colimit.desc _ (moduleSemifreeResolutionTailCocone A D M c)
  fac c k := by
    cases k with
    | zero =>
      change (moduleDiskCoverBoundary A D M ≫ moduleResolutionCandidateι A D M 0) ≫
        colimit.desc _ (moduleSemifreeResolutionTailCocone A D M c) = c.ι.app 0
      have hf : moduleResolutionCandidateι A D M 0 ≫
          colimit.desc _ (moduleSemifreeResolutionTailCocone A D M c) = c.ι.app 1 :=
        colimit.ι_desc (moduleSemifreeResolutionTailCocone A D M c) 0
      have h := c.w (homOfLE (Nat.le_succ 0))
      have h0 : moduleDiskCoverBoundary A D M ≫ c.ι.app 1 = c.ι.app 0 := by
        simp only [moduleSemifreeResolutionDiagram,
          Functor.ofSequence_map_homOfLE_succ] at h
        change moduleDiskCoverBoundary A D M ≫ c.ι.app 1 = c.ι.app 0 at h
        exact h
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun b => moduleDiskCoverBoundary A D M ≫ b) hf).trans h0)
    | succ k => exact colimit.ι_desc (moduleSemifreeResolutionTailCocone A D M c) k
  uniq c b h := by
    apply colimit.hom_ext (F := moduleResolutionDiagram A D M)
    intro k
    exact (h (k + 1)).trans (colimit.ι_desc (moduleSemifreeResolutionTailCocone A D M c) k).symm

def moduleSemifreeResolutionQuotient (M : ModuleCategory A D) : ℕ → ModuleCategory A D
  | 0 => ∐ moduleDiskCoverLowerFamily A D M
  | k + 1 => (moduleKernelCellSource A D (moduleResolutionStage A D M k).hom)⟦(1 : ℤ)⟧

def moduleSemifreeResolutionQuotientMap (M : ModuleCategory A D) (k : ℕ) :
    moduleSemifreeResolutionStage A D M (k + 1) ⟶ moduleSemifreeResolutionQuotient A D M k :=
  match k with
  | 0 => moduleDiskCoverQuotient A D M
  | k + 1 => moduleKernelCellStepQuotient A D (moduleResolutionStage A D M k).hom

def moduleSemifreeResolutionSplit (M : ModuleCategory A D) (k : ℕ) :
    ModuleGradedSplit A D (moduleSemifreeResolutionTransition A D M k)
      (moduleSemifreeResolutionQuotientMap A D M k) :=
  match k with
  | 0 => moduleDiskCoverGradedSplit A D M
  | k + 1 => moduleKernelCellStepGradedSplit A D (moduleResolutionStage A D M k).hom

def moduleSemifreeResolutionInitial (M : ModuleCategory A D) :
    ModuleSphereFreePresentation A D (moduleSemifreeResolutionStage A D M 0) where
  Index := ModuleDiskCoverIndex A D M
  object := fun t => t.1
  degree := fun t => t.2.1 + 1
  iso := Iso.refl _

def moduleSemifreeResolutionQuotientPresentation (M : ModuleCategory A D) (k : ℕ) :
    ModuleSphereFreePresentation A D (moduleSemifreeResolutionQuotient A D M k) := by
  cases k with
  | zero => exact
      { Index := ModuleDiskCoverIndex A D M
        object := fun t => t.1
        degree := fun t => t.2.1
        iso := Iso.refl _ }
  | succ k => exact
      { Index := ModuleKernelCellIndex A D (moduleResolutionStage A D M k).hom
        object := fun t => t.1
        degree := fun t => t.2.1
        iso := moduleKernelCellQuotientFreeIso A D (moduleResolutionStage A D M k).hom }

/-- 既存の可算cell候補の、実際のsemifree filtration。 -/
def moduleResolutionSemifreeFiltration (M : ModuleCategory A D) :
    ModuleSemifreeFiltration A D (moduleResolutionCandidate A D M) where
  stage := moduleSemifreeResolutionStage A D M
  transition := moduleSemifreeResolutionTransition A D M
  initial := moduleSemifreeResolutionInitial A D M
  quotient := moduleSemifreeResolutionQuotient A D M
  quotientMap := moduleSemifreeResolutionQuotientMap A D M
  split := moduleSemifreeResolutionSplit A D M
  quotientPresentation := moduleSemifreeResolutionQuotientPresentation A D M
  cocone := moduleSemifreeResolutionCocone A D M
  isColimit := moduleSemifreeResolutionIsColimit A D M
  iso := Iso.refl _

lemma moduleResolutionCandidate_semifree (M : ModuleCategory A D) :
    moduleSemifree A D (moduleResolutionCandidate A D M) :=
  ⟨moduleResolutionSemifreeFiltration A D M⟩

/-- 任意dg加群には、次数ごと全射かつ準同型なsemifree解像度が存在する。 -/
theorem exists_semifree_resolution (M : ModuleCategory A D) :
    ∃ (P : ModuleCategory A D) (q : P ⟶ M),
      moduleSemifree A D P ∧ moduleDegreewiseSurjective A D q ∧ moduleQuasiIso A D q :=
  ⟨moduleResolutionCandidate A D M, moduleResolutionCandidateπ A D M,
    moduleResolutionCandidate_semifree A D M,
    moduleResolutionCandidateπ_degreewiseSurjective A D M,
    moduleResolutionCandidateπ_quasiIso A D M⟩

end SerrePositivity.DifferentialGraded
end

end Resolution
