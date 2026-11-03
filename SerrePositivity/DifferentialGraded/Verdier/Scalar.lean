module

public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.BalancedTensor
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.CategoriesAndModules
public import SerrePositivity.DifferentialGraded.Module.Functor
public import SerrePositivity.DifferentialGraded.Module.Graded
public import Mathlib.CategoryTheory.Adjunction.Unique
public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.EnhancementComparison
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKernel
public import SerrePositivity.DifferentialGraded.Morita.Perfect
public import SerrePositivity.DifferentialGraded.Endomorphism.Perfect
public import SerrePositivity.CategoryTheory.Triangulated.VerdierLift
public import SerrePositivity.CategoryTheory.Karoubi.Triangulated
public import SerrePositivity.DifferentialGraded.Verdier.Comparison
public import SerrePositivity.DifferentialGraded.Quotient.Path.Evaluation
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraph
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Equivalence
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
public import SerrePositivity.DifferentialGraded.Verdier.Derived

/-!
# Verdier.Scalar

## 概要
10 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## ScalarGraphRestriction（旧 SerrePositivity/DifferentialGraded/Verdier/ScalarGraphRestriction.lean） -/

/-! # 係数変更と graph 制限・通常の延長の交換

係数環の平坦性を仮定せず、通常の随伴と実際の制限を先に比較する。
-/

@[expose] public section ScalarGraphRestriction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

private lemma scalarGraph_postcompose_id (P Q : Complex A) :
    homPostcompose P (𝟙 Q) = 𝟙 _ := (homFunctor P).map_id Q

private lemma scalarGraph_precompose_id (P Q : Complex A) :
    homPrecompose (𝟙 P) Q = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact CochainComplex.HomComplex.Cochain.id_comp z

/-- 係数制限と dg 関手への制限は、全次数の加群作用も含めて可換する。 -/
def scalarGraphRestrictionIso :
    moduleRestriction A' (ScalarExtension.DGBaseChange φ D) (ScalarExtension.DGBaseChange φ E)
        (ScalarExtension.dgFunctor φ F).op ⋙ ScalarExtension.moduleRestriction φ D ≅
      ScalarExtension.moduleRestriction φ E ⋙ moduleRestriction A D E F.op :=
  NatIso.ofComponents (fun M => moduleIsoMk A D (fun _ => Iso.refl _) (by
    intro x y
    dsimp only [Iso.refl_hom]
    rw [scalarGraph_postcompose_id, scalarGraph_precompose_id]
    simp only [Category.comp_id]
    change (ScalarExtension.rightRestriction φ D
      (restrictModule A' (ScalarExtension.DGBaseChange φ D) (ScalarExtension.DGBaseChange φ E)
        (ScalarExtension.dgFunctor φ F).op (ForgetEnrichment.to (Complex A') M))).map x y =
      F.op.map x y ≫
        (ScalarExtension.rightRestriction φ E (ForgetEnrichment.to (Complex A') M)).map
          (F.op.obj x) (F.op.obj y)
    rw [ScalarExtension.rightRestriction_map, ScalarExtension.rightRestriction_map]
    change (ScalarExtension.adjunction φ).unit.app _ ≫
        (ScalarExtension.restriction φ).map
          ((ScalarExtension.extension φ).map (F.op.map x y) ≫
            (ForgetEnrichment.to (Complex A') M).map _ _) ≫ _ = _
    rw [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
    have hn := (ScalarExtension.adjunction φ).unit.naturality (F.op.map x y)
    simp only [Functor.comp_map, Functor.id_map] at hn
    have hh := congrArg (fun t => t ≫
      (ScalarExtension.restriction φ).map
        ((ForgetEnrichment.to (Complex A') M).map (F.op.obj x) (F.op.obj y)) ≫
      ScalarExtension.restrictionHom φ
        ((ForgetEnrichment.to (Complex A') M).obj (F.op.obj x))
        ((ForgetEnrichment.to (Complex A') M).obj (F.op.obj y))) hn.symm
    simp only [Category.assoc] at hh
    convert hh using 1 <;> rfl))
    (by
      intro M N f
      apply moduleMorphism_ext
      intro d
      simp only [Functor.comp_map, CategoryTheory.Functor.map_comp,
        moduleIsoMk_hom_eval, Iso.refl_hom, ScalarExtension.moduleRestriction_eval,
        moduleRestriction_map_eval]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- 両複合随伴の一意性で得る、通常の graph 延長と係数拡大の交換。 -/
def scalarGraphExtensionIso :
    (dgModuleExtension A D E F).onClosed ⋙ ScalarExtension.moduleExtension φ E ≅
      ScalarExtension.moduleExtension φ D ⋙
        (dgModuleExtension A' (ScalarExtension.DGBaseChange φ D) (ScalarExtension.DGBaseChange φ E)
          (ScalarExtension.dgFunctor φ F)).onClosed :=
  Adjunction.leftAdjointUniq
    ((dgModuleExtensionRestrictionAdjunction A D E F).comp
      (ScalarExtension.moduleAdjunction φ E))
    (((ScalarExtension.moduleAdjunction φ D).comp
      (dgModuleExtensionRestrictionAdjunction A' (ScalarExtension.DGBaseChange φ D)
        (ScalarExtension.DGBaseChange φ E) (ScalarExtension.dgFunctor φ F))).ofNatIsoRight
      (scalarGraphRestrictionIso φ D E F))
end SerrePositivity.DifferentialGraded
end

end ScalarGraphRestriction

/-! ## ProjectiveResolutionComparison（旧 SerrePositivity/DifferentialGraded/Verdier/ProjectiveResolutionComparison.lean） -/

/-! # 実際の射影解像度関手と、射影的ホモトピー圏からの三角同値の逆関手 -/

@[expose] public section ProjectiveResolutionComparison
universe u v

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance projectiveModuleHomotopyToDerivedEssSurj :
    (projectiveModuleHomotopyToDerived A D).EssSurj where
  mem_essImage X := by
    obtain ⟨⟨M⟩⟩ := X
    let R := moduleCanonicalProjectiveResolution A D M
    refine ⟨⟨(moduleToHomotopy A D).obj R.obj, R.projective⟩, ⟨?_⟩⟩
    exact (moduleToHomotopyDerivedIso A D).app R.obj ≪≫ moduleDerivedIso A D R.π R.quasiIso

instance projectiveModuleHomotopyToDerivedIsEquivalence :
    (projectiveModuleHomotopyToDerived A D).IsEquivalence where

def projectiveModuleDerivedEquivalence :
    projectiveModuleHomotopyCategory A D ≌ DerivedModuleCategory A D :=
  (projectiveModuleHomotopyToDerived A D).asEquivalence

instance projectiveModuleDerivedEquivalenceFunctorCommShift :
    (projectiveModuleDerivedEquivalence A D).functor.CommShift ℤ :=
  projectiveModuleHomotopyToDerivedCommShift A D
instance projectiveModuleDerivedEquivalenceInverseCommShift :
    (projectiveModuleDerivedEquivalence A D).inverse.CommShift ℤ :=
  (projectiveModuleDerivedEquivalence A D).commShiftInverse ℤ
instance projectiveModuleDerivedEquivalenceCommShift :
    (projectiveModuleDerivedEquivalence A D).CommShift ℤ :=
  (projectiveModuleDerivedEquivalence A D).commShift_of_functor ℤ
instance projectiveModuleDerivedEquivalenceIsTriangulated :
    (projectiveModuleDerivedEquivalence A D).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (projectiveModuleHomotopyToDerivedIsTriangulated A D)

variable (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)

lemma derivedResolution_projective (X : DerivedModuleCategory A D) :
    moduleHomotopyProjectiveLocus A D ((moduleDerivedResolutionFunctor A D R).obj X) := by
  obtain ⟨⟨M⟩⟩ := X
  exact (moduleHomotopyProjectiveLocus A D).prop_of_iso
    (moduleDerivedResolutionComputation A D R M).symm (R M).projective

def derivedResolutionToProjectives :
    DerivedModuleCategory A D ⥤ projectiveModuleHomotopyCategory A D :=
  (moduleHomotopyProjectiveLocus A D).lift (moduleDerivedResolutionFunctor A D R)
    (derivedResolution_projective A D R)

def derivedResolutionToProjectivesInverseIso :
    derivedResolutionToProjectives A D R ≅ (projectiveModuleDerivedEquivalence A D).inverse :=
  ((whiskeringRight _ _ _).obj (projectiveModuleDerivedEquivalence A D).functor).preimageIso
    (Morita.kernelInputResolutionDerivedCounitIso A D R ≪≫
      (projectiveModuleDerivedEquivalence A D).counitIso.symm)

/-- 元の入力解像度関手そのものは、三角同値の逆関手を包含したものと自然同型。 -/
def derivedResolutionProjectiveComparison :
    moduleDerivedResolutionFunctor A D R ≅
      (projectiveModuleDerivedEquivalence A D).inverse ⋙ (moduleHomotopyProjectiveLocus A D).ι :=
  ((moduleHomotopyProjectiveLocus A D).liftCompιIso _ _).symm ≪≫
    isoWhiskerRight (derivedResolutionToProjectivesInverseIso A D R)
      (moduleHomotopyProjectiveLocus A D).ι
end SerrePositivity.DifferentialGraded
end

end ProjectiveResolutionComparison

/-! ## KernelActionTriangles（旧 SerrePositivity/DifferentialGraded/Verdier/KernelActionTriangles.lean） -/

/-! # 主導来 kernel の実際の作用の三角性

任意の通常 kernel の tensor dg 関手を射影的ホモトピー圏上で計算し、
既存の入力解像度による作用との自然同型で構造を運ぶ。dg 圏の分解を使わない。
-/

@[expose] public section KernelActionTriangles
universe u v w

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

local instance kernelTrianglesHomotopyCommShift : (kernelTensor A D E P).onHomotopy.CommShift ℤ :=
  dgModuleFunctorHomotopyCommShift A D E (kernelTensor A D E P)
local instance kernelTrianglesHomotopyIsTriangulated :
    (kernelTensor A D E P).onHomotopy.IsTriangulated :=
  dgModuleFunctorHomotopyIsTriangulated A D E (kernelTensor A D E P)

def kernelProjectiveActionModel : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E :=
  (projectiveModuleDerivedEquivalence A D).inverse ⋙ (moduleHomotopyProjectiveLocus A D).ι ⋙
    (kernelTensor A D E P).onHomotopy ⋙ moduleHomotopyToDerivedClosed A E

instance kernelProjectiveActionModelCommShift :
    (kernelProjectiveActionModel A D E P).CommShift ℤ := by
  dsimp [kernelProjectiveActionModel]
  infer_instance
instance kernelProjectiveActionModelIsTriangulated :
    (kernelProjectiveActionModel A D E P).IsTriangulated := by
  dsimp [kernelProjectiveActionModel]
  infer_instance

/-- 入力解像度による実際の作用と、射影的ホモトピー圏上の計算の自然同型。 -/
def kernelProjectiveActionComparison :
    kernelDerivedTensorOnBimodule A D E P ≅ kernelProjectiveActionModel A D E P :=
  isoWhiskerRight
    (derivedResolutionProjectiveComparison A D (moduleCanonicalProjectiveResolution A D))
    (kernelHomotopyToDerived A D E P) ≪≫ Functor.associator _ _ _

/-- まだ構造を持たない実作用に、実際の tensor dg 関手から shift 構造を与える。 -/
@[instance_reducible]
def kernelOnBimoduleActionCommShift : (kernelDerivedTensorOnBimodule A D E P).CommShift ℤ :=
  Functor.CommShift.ofIso (kernelProjectiveActionComparison A D E P).symm ℤ

lemma kernelOnBimoduleActionIsTriangulated :
    letI := kernelOnBimoduleActionCommShift A D E P
    (kernelDerivedTensorOnBimodule A D E P).IsTriangulated := by
  let := kernelOnBimoduleActionCommShift A D E P
  let := Functor.CommShift.ofIso_compatibility (kernelProjectiveActionComparison A D E P).symm ℤ
  exact Functor.isTriangulated_of_iso (kernelProjectiveActionComparison A D E P).symm

variable (K : Kernel A D E)

/-- 主局所化上の kernel の作用にも、同じ計算から整数 shift を与える。 -/
@[instance_reducible]
def mainKernelActionCommShift : (kernelDerivedTensor A D E K).CommShift ℤ := by
  obtain ⟨⟨Q⟩⟩ := K
  letI := kernelOnBimoduleActionCommShift A D E (BimoduleCategory.underlying A E D Q)
  exact Functor.CommShift.ofIso (kernelDerivedTensorOnBimoduleIso A D E Q).symm ℤ

lemma mainKernelActionIsTriangulated :
    letI := mainKernelActionCommShift A D E K
    (kernelDerivedTensor A D E K).IsTriangulated := by
  obtain ⟨⟨Q⟩⟩ := K
  let := kernelOnBimoduleActionCommShift A D E (BimoduleCategory.underlying A E D Q)
  let := kernelOnBimoduleActionIsTriangulated A D E (BimoduleCategory.underlying A E D Q)
  let := mainKernelActionCommShift A D E ((bimoduleToDerived A E D).obj Q)
  let := Functor.CommShift.ofIso_compatibility (kernelDerivedTensorOnBimoduleIso A D E Q).symm ℤ
  exact Functor.isTriangulated_of_iso (kernelDerivedTensorOnBimoduleIso A D E Q).symm

@[instance_reducible]
def mainPerfectKernelActionCommShift (hK : kernelColumnsPerfect A D E K) :
    (perfectDerivedKernelAction A D E K hK).CommShift ℤ := by
  letI := mainKernelActionCommShift A D E K
  dsimp [perfectDerivedKernelAction, perfectFunctorRestriction, perfectModuleInclusion]
  infer_instance

lemma mainPerfectKernelActionIsTriangulated (hK : kernelColumnsPerfect A D E K) :
    letI := mainPerfectKernelActionCommShift A D E K hK
    (perfectDerivedKernelAction A D E K hK).IsTriangulated := by
  let := mainKernelActionCommShift A D E K
  let := mainKernelActionIsTriangulated A D E K
  dsimp [mainPerfectKernelActionCommShift, perfectDerivedKernelAction,
    perfectFunctorRestriction, perfectModuleInclusion]
  infer_instance

/-- 指定列の Perf 条件から、殺す生成集合の thick 閉包の像を判定する。 -/
lemma mainKernelAction_perfectOver (S : Set D) (T : Set E)
    (hST : ∀ d ∈ S, modulePerfectOver A E T ((kernelDerivedColumn A D E d).obj K))
    {X : DerivedModuleCategory A D} (hX : modulePerfectOver A D S X) :
    modulePerfectOver A E T ((kernelDerivedTensor A D E K).obj X) := by
  let := mainKernelActionCommShift A D E K
  let := mainKernelActionIsTriangulated A D E K
  let N := (modulePerfectOver A E T).inverseImage (kernelDerivedTensor A D E K)
  have : N.IsTriangulated := by dsimp [N]; infer_instance
  have : N.IsClosedUnderIsomorphisms := by dsimp [N]; infer_instance
  have : N.IsStableUnderRetracts :=
    ⟨fun r hY => (modulePerfectOver A E T).prop_of_retract
      (r.map (kernelDerivedTensor A D E K)) hY⟩
  exact ((modulePerfectOver_le_iff_generators A D N S).2 (fun d hd =>
    (modulePerfectOver A E T).prop_of_iso (kernelDerivedColumnActionIso A D E K d).symm
      (hST d hd))) X hX
end SerrePositivity.DifferentialGraded
end

end KernelActionTriangles

/-! ## PerfectKernelVerdier（旧 SerrePositivity/DifferentialGraded/Verdier/PerfectKernelVerdier.lean） -/

/-! # 指定生成集合を対応させる主導来 kernel の実際の Perf–Verdier 関手 -/

@[expose] public section PerfectKernelVerdier
universe u v w

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Limits Idempotents Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全 Perf の中で、指定集合 S から生成される厚い零対象クラス。 -/
def perfectNullObjects (S : Set D) : ObjectProperty (PerfectModuleCategory A D) :=
  (modulePerfectOver A D S).inverseImage (modulePerfectOver A D Set.univ).ι

instance perfectNullObjectsIsTriangulated (S : Set D) :
    (perfectNullObjects A D S).IsTriangulated := by
  dsimp [perfectNullObjects]
  infer_instance

abbrev PerfectVerdierQuotient (S : Set D) := (perfectNullObjects A D S).trW.Localization
abbrev perfectVerdierQuotient (S : Set D) :
    PerfectModuleCategory A D ⥤ PerfectVerdierQuotient A D S :=
  (perfectNullObjects A D S).trW.Q

variable (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)
  (hK : kernelColumnsPerfect A D E K) (S : Set D) (T : Set E)
  (hST : ∀ d ∈ S, modulePerfectOver A E T ((kernelDerivedColumn A D E d).obj K))

local instance perfectKernelVerdierShift : (perfectDerivedKernelAction A D E K hK).CommShift ℤ :=
  mainPerfectKernelActionCommShift A D E K hK
local instance perfectKernelVerdierTriangles :
    (perfectDerivedKernelAction A D E K hK).IsTriangulated :=
  mainPerfectKernelActionIsTriangulated A D E K hK

include hST in
lemma perfectKernelNullObjects_image (X : PerfectModuleCategory A D)
    (hX : perfectNullObjects A D S X) :
    perfectNullObjects A E T ((perfectDerivedKernelAction A D E K hK).obj X) :=
  mainKernelAction_perfectOver A D E K S T hST hX

include hST in
lemma perfectKernelVerdier_kills (X : PerfectModuleCategory A D) (hX : perfectNullObjects A D S X) :
    IsZero ((perfectVerdierQuotient A E T).obj
      ((perfectDerivedKernelAction A D E K hK).obj X)) :=
  verdierQuotient_isZero (perfectNullObjects A E T) _
    (perfectKernelNullObjects_image A D E K hK S T hST X hX)

/-- 元の実際の主 Perf 作用を先に Verdier 局所化して得る関手。 -/
def perfectKernelVerdierFunctor : PerfectVerdierQuotient A D S ⥤ PerfectVerdierQuotient A E T :=
  verdierLift (perfectNullObjects A D S)
    (perfectDerivedKernelAction A D E K hK ⋙ perfectVerdierQuotient A E T)
    (perfectKernelVerdier_kills A D E K hK S T hST)

/-- 主導来 kernel の Perf 作用と標準商関手の実際の因子化正方形。 -/
def perfectKernelVerdierSquare :
    perfectVerdierQuotient A D S ⋙ perfectKernelVerdierFunctor A D E K hK S T hST ≅
      perfectDerivedKernelAction A D E K hK ⋙ perfectVerdierQuotient A E T :=
  verdierLiftFactors _ _ (perfectKernelVerdier_kills A D E K hK S T hST)

instance perfectKernelVerdierFunctorCommShift :
    (perfectKernelVerdierFunctor A D E K hK S T hST).CommShift ℤ := by
  dsimp [perfectKernelVerdierFunctor]
  infer_instance
instance perfectKernelVerdierSquareCommShift :
    NatTrans.CommShift (perfectKernelVerdierSquare A D E K hK S T hST).hom ℤ := by
  dsimp [perfectKernelVerdierSquare]
  infer_instance
instance perfectKernelVerdierFunctorIsTriangulated :
    (perfectKernelVerdierFunctor A D E K hK S T hST).IsTriangulated := by
  dsimp [perfectKernelVerdierFunctor]
  infer_instance

def perfectKernelCompletedVerdierFunctor :
    Karoubi (PerfectVerdierQuotient A D S) ⥤ Karoubi (PerfectVerdierQuotient A E T) :=
  (functorExtension₂ _ _).obj (perfectKernelVerdierFunctor A D E K hK S T hST)

def perfectKernelVerdierSquareTriangle :=
  Functor.mapTriangleIso (perfectKernelVerdierSquare A D E K hK S T hST)
end SerrePositivity.DifferentialGraded
end

end PerfectKernelVerdier

/-! ## RetractSquare（旧 SerrePositivity/DifferentialGraded/Verdier/RetractSquare.lean） -/

/-! # 局所商比較の retract 図式と Karoubi の形式的直和因子 -/

@[expose] public section RetractSquare
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Idempotents

section General
variable {C T : Type*} [Category* C] [Category* T] (F : C ⥤ T) [F.Full] [F.Faithful]
  {X Y : C}

/-- 完全忠実な比較の像の間の retract を、両方の分裂射ごと引き戻す。 -/
def comparisonRetractPreimage (r : Retract (F.obj X) (F.obj Y)) : Retract X Y where
  i := F.preimage r.i
  r := F.preimage r.r
  retract := by
    apply F.map_injective
    rw [CategoryTheory.Functor.map_comp, F.map_preimage, F.map_preimage,
      CategoryTheory.Functor.map_id]
    exact r.retract

lemma comparisonRetract_i_square (r : Retract (F.obj X) (F.obj Y)) :
    F.map (comparisonRetractPreimage F r).i = r.i := F.map_preimage _

lemma comparisonRetract_r_square (r : Retract (F.obj X) (F.obj Y)) :
    F.map (comparisonRetractPreimage F r).r = r.r := F.map_preimage _

lemma comparisonRetract_iff :
    Nonempty (Retract (F.obj X) (F.obj Y)) ↔ Nonempty (Retract X Y) :=
  ⟨fun ⟨r⟩ => ⟨comparisonRetractPreimage F r⟩, fun ⟨r⟩ => ⟨r.map F⟩⟩
end General

namespace DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (S : Set D) (h : localKFlat A D S)

/-- 局所 tria 商比較は retract 関係を保存し反映する。 -/
lemma localTriaRetract_iff (X Y : TriaQuotient A D S) :
    Nonempty (Retract ((localQuotientTriaEquivalence A D S h).functor.obj X)
      ((localQuotientTriaEquivalence A D S h).functor.obj Y)) ↔ Nonempty (Retract X Y) :=
  comparisonRetract_iff (localQuotientTriaEquivalence A D S h).functor

/-- perfect enhancement と完備商の比較も retract 関係を保存し反映する。 -/
lemma localPerfectRetract_iff
    (X Y : PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ) :
    Nonempty (Retract ((localPerfectQuotientEquivalence A D S h).functor.obj X)
      ((localPerfectQuotientEquivalence A D S h).functor.obj Y)) ↔ Nonempty (Retract X Y) :=
  comparisonRetract_iff (localPerfectQuotientEquivalence A D S h).functor

/-- 完備化された比較に沿う、形式的冪等元の分裂の図式。 -/
def localCompletedRetract (P : CompletedTriaQuotient A D S) :=
  (karoubiRetract P).map (localCompletedQuotientEquivalence A D S h).functor

lemma localCompletedRetract_i (P : CompletedTriaQuotient A D S) :
    (localCompletedRetract A D S h P).i.f = (localQuotientTriaFunctor A D S).map P.p := rfl

lemma localCompletedRetract_r (P : CompletedTriaQuotient A D S) :
    (localCompletedRetract A D S h P).r.f = (localQuotientTriaFunctor A D S).map P.p := rfl

lemma localCompletedRetract_split (P : CompletedTriaQuotient A D S) :
    (localCompletedRetract A D S h P).i ≫ (localCompletedRetract A D S h P).r =
      𝟙 ((localCompletedQuotientEquivalence A D S h).functor.obj P) :=
  (localCompletedRetract A D S h P).retract
end DGQuotient
end SerrePositivity.DifferentialGraded
end

end RetractSquare

/-! ## ScalarExtensionSquare（旧 SerrePositivity/DifferentialGraded/Verdier/ScalarExtensionSquare.lean） -/

/-! # 非平坦係数変更と局所 perfect・完備 Verdier 商比較

U12f の実際の導来係数拡大と U15d の固定 path 比較を使う。
完備商上の関手は既存の局所 perfect 同値に沿って運ぶ。
これを未完備 tria の Verdier 局所化から直接構成した関手と同一視しない。
-/

@[expose] public section ScalarExtensionSquare
universe u v

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory CategoryTheory.Functor ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D] (S : Set D)

/-- 商の係数変更を行い、固定 path 比較の dg 関手に沿って延長した実際の Perf 関手。 -/
def quotientScalarPerfectFunctor :
    PerfectModuleCategory A (QuotientObject D S) ⥤
      PerfectModuleCategory A' (QuotientObject (DGBaseChange φ D) S) :=
  perfectScalarDerivedExtension φ (QuotientObject D S) Set.univ ⋙
    quasiEquivalencePerfectExtension A' (DGBaseChange φ (QuotientObject D S))
      (QuotientObject (DGBaseChange φ D) S) (quotientBaseChangeDGFunctor φ D S)

instance quotientScalarPerfectFunctorCommShift :
    (quotientScalarPerfectFunctor φ D S).CommShift ℤ := by
  letI := perfectScalarDerivedExtensionCommShift φ (QuotientObject D S) Set.univ
  letI := quasiEquivalencePerfectExtensionCommShift A'
    (DGBaseChange φ (QuotientObject D S)) (QuotientObject (DGBaseChange φ D) S)
    (quotientBaseChangeDGFunctor φ D S)
  dsimp [quotientScalarPerfectFunctor]
  infer_instance

instance quotientScalarPerfectFunctorIsTriangulated :
    (quotientScalarPerfectFunctor φ D S).IsTriangulated := by
  let := perfectScalarDerivedExtensionCommShift φ (QuotientObject D S) Set.univ
  let := quasiEquivalencePerfectExtensionCommShift A'
    (DGBaseChange φ (QuotientObject D S)) (QuotientObject (DGBaseChange φ D) S)
    (quotientBaseChangeDGFunctor φ D S)
  let := perfectScalarDerivedExtensionIsTriangulated φ (QuotientObject D S) Set.univ
  let := quasiEquivalencePerfectExtensionIsTriangulated A'
    (DGBaseChange φ (QuotientObject D S)) (QuotientObject (DGBaseChange φ D) S)
    (quotientBaseChangeDGFunctor φ D S)
  dsimp [quotientScalarPerfectFunctor]
  infer_instance

/-- Perf への制限を忘れると、U12f と U15d の実際の導来関手の合成に戻る。 -/
def quotientScalarPerfectInclusionIso :
    quotientScalarPerfectFunctor φ D S ⋙
        perfectModuleInclusion A' (QuotientObject (DGBaseChange φ D) S) Set.univ ≅
      perfectModuleInclusion A (QuotientObject D S) Set.univ ⋙
        derivedExtension φ (QuotientObject D S) ⋙
          dgDerivedExtension A' (DGBaseChange φ (QuotientObject D S))
            (QuotientObject (DGBaseChange φ D) S) (quotientBaseChangeDGFunctor φ D S) :=
  Iso.refl _

/-- 同じ係数変更を、既存の perfect enhancement の H⁰ に運んだ関手。 -/
def quotientScalarPerfectHomotopyFunctor :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ⥤
      PerfectDGHomotopyCategoryOver A' (QuotientObject (DGBaseChange φ D) S) Set.univ :=
  (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor ⋙
    quotientScalarPerfectFunctor φ D S ⋙
      (perfectDGModuleHomotopyEquivalence A'
        (QuotientObject (DGBaseChange φ D) S) Set.univ).inverse

instance quotientScalarPerfectHomotopyFunctorCommShift :
    (quotientScalarPerfectHomotopyFunctor φ D S).CommShift ℤ := by
  dsimp [quotientScalarPerfectHomotopyFunctor]
  infer_instance

instance quotientScalarPerfectHomotopyFunctorIsTriangulated :
    (quotientScalarPerfectHomotopyFunctor φ D S).IsTriangulated := by
  dsimp [quotientScalarPerfectHomotopyFunctor]
  infer_instance

def quotientScalarPerfectHomotopySquare :
    quotientScalarPerfectHomotopyFunctor φ D S ⋙
        (perfectDGModuleHomotopyEquivalence A'
          (QuotientObject (DGBaseChange φ D) S) Set.univ).functor ≅
      (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor ⋙
        quotientScalarPerfectFunctor φ D S :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (perfectDGModuleHomotopyEquivalence A'
        (QuotientObject (DGBaseChange φ D) S) Set.univ).counitIso ≪≫
          Functor.rightUnitor _)

instance quotientScalarPerfectHomotopySquareCommShift :
    NatTrans.CommShift (quotientScalarPerfectHomotopySquare φ D S).hom ℤ := by
  dsimp only [quotientScalarPerfectHomotopySquare, Iso.trans_hom,
    isoWhiskerLeft_hom]
  infer_instance

def quotientScalarPerfectHomotopySquareTriangle :=
  Functor.mapTriangleIso (quotientScalarPerfectHomotopySquare φ D S)

variable (h : localKFlat A D S) (h' : localKFlat A' (DGBaseChange φ D) S)

/-- 完備 Verdier 商上の導来係数変更。両係数環での局所 K-flat 条件は別に受け取る。 -/
def completedScalarExtension :
    CompletedTriaQuotient A D S ⥤ CompletedTriaQuotient A' (DGBaseChange φ D) S :=
  (localPerfectQuotientEquivalence A D S h).inverse ⋙
    quotientScalarPerfectHomotopyFunctor φ D S ⋙
      (localPerfectQuotientEquivalence A' (DGBaseChange φ D) S h').functor

instance completedScalarExtensionCommShift :
    (completedScalarExtension φ D S h h').CommShift ℤ := by
  dsimp [completedScalarExtension]
  infer_instance

instance completedScalarExtensionIsTriangulated :
    (completedScalarExtension φ D S h h').IsTriangulated := by
  dsimp [completedScalarExtension]
  infer_instance

/-- 局所 perfect 比較と完備商上の係数変更の可換正方形。 -/
def localPerfectScalarExtensionSquare :
    (localPerfectQuotientEquivalence A D S h).functor ⋙
        completedScalarExtension φ D S h h' ≅
      quotientScalarPerfectHomotopyFunctor φ D S ⋙
        (localPerfectQuotientEquivalence A' (DGBaseChange φ D) S h').functor :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (localPerfectQuotientEquivalence A D S h).unitIso.symm _ ≪≫
      Functor.leftUnitor _

instance localPerfectScalarExtensionSquareCommShift :
    NatTrans.CommShift (localPerfectScalarExtensionSquare φ D S h h').hom ℤ := by
  dsimp only [localPerfectScalarExtensionSquare, Iso.trans_hom, isoWhiskerRight_hom]
  infer_instance

def localPerfectScalarExtensionSquareTriangle :=
  Functor.mapTriangleIso (localPerfectScalarExtensionSquare φ D S h h')
end SerrePositivity.DifferentialGraded.DGQuotient
end

end ScalarExtensionSquare

/-! ## ScalarExtensionTria（旧 SerrePositivity/DifferentialGraded/Verdier/ScalarExtensionTria.lean） -/

/-! # 未完備の局所商・指定 Verdier 比較と非平坦係数変更

明示的 dg 商上の実際の導来係数変更を tria に制限し、局所商同値に沿って運ぶ。
元の dg 圏の tria 上の係数変更を先に Verdier 局所化する構成との一致は含めない。
-/

@[expose] public section ScalarExtensionTria
universe u v w

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- retract を加える前の tria から Perf への実際の包含。 -/
def triaToPerfect : TriaCategory A D ⥤ PerfectModuleCategory A D :=
  (modulePerfect A D).lift (triaInclusion A D)
    (fun X => (derivedFiniteCellOver A D Set.univ).le_retractClosure _ X.property)

instance triaToPerfectCommShift : (triaToPerfect A D).CommShift ℤ := by
  dsimp [triaToPerfect]
  infer_instance

instance triaToPerfectIsTriangulated : (triaToPerfect A D).IsTriangulated := by
  dsimp [triaToPerfect]
  infer_instance

section General
variable {A' : Type u} [CommRing A'] (E : Type w) [DGCategory A' E] [Small.{u} E]
  (T : PerfectModuleCategory A D ⥤ PerfectModuleCategory A' E)
  [T.CommShift ℤ] [T.IsTriangulated]

/-- 代表加群を tria に送る完全関手は、tria 全体を tria に送る。 -/
lemma exactPerfectFunctor_tria
    (hgen : ∀ d : D, derivedFiniteCellOver A' E Set.univ
      (T.obj ((triaToPerfect A D).obj (triaRepresentable A D d))).obj)
    (X : TriaCategory A D) :
    derivedFiniteCellOver A' E Set.univ (T.obj ((triaToPerfect A D).obj X)).obj := by
  let P := (derivedFiniteCellOver A' E Set.univ).inverseImage
    (triaToPerfect A D ⋙ T ⋙ (modulePerfect A' E).ι)
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  exact ((triaImage_le_iff_generators A D Set.univ P).2 (fun d _ => hgen d)) X X.property
end General

namespace DGQuotient
variable {A D} {A' : Type u} [CommRing A'] (φ : A →+* A') (S : Set D)

/-- 係数変更と固定 path の dg 比較を合成すると、同じ対象の代表加群になる。 -/
def quotientScalarRepresentableIso (z : QuotientObject D S) :
    ((quotientScalarPerfectFunctor φ D S).obj
      ((triaToPerfect A (QuotientObject D S)).obj
        (triaRepresentable A (QuotientObject D S) z))).obj ≅
      (triaRepresentable A' (QuotientObject (ScalarExtension.DGBaseChange φ D) S)
        ⟨z.val⟩).obj := by
  let Q := QuotientObject D S
  let Q' := QuotientObject (ScalarExtension.DGBaseChange φ D) S
  let M := ForgetEnrichment.of (Complex A) (representable A z)
  let e : (ScalarExtension.moduleExtension φ Q).obj M ≅
      ForgetEnrichment.of (Complex A')
        (representable A' (show ScalarExtension.DGBaseChange φ Q from z)) :=
    eqToIso (by
      change ForgetEnrichment.of (Complex A')
        (ScalarExtension.rightModule φ Q (representable A z)) = _
      rw [scalarRepresentable_eq])
  exact (dgDerivedExtension A' (ScalarExtension.DGBaseChange φ Q) Q'
    (quotientBaseChangeDGFunctor φ D S)).mapIso
      (scalarDerivedProjectiveComputation φ Q M (representable_homotopicallyProjective A Q z) ≪≫
        (moduleToDerived A' (ScalarExtension.DGBaseChange φ Q)).mapIso e) ≪≫
    dgDerivedExtensionRepresentableIso A' (ScalarExtension.DGBaseChange φ Q) Q'
      (quotientBaseChangeDGFunctor φ D S) z

lemma quotientScalarPerfect_tria (X : TriaCategory A (QuotientObject D S)) :
    derivedFiniteCellOver A' (QuotientObject (ScalarExtension.DGBaseChange φ D) S) Set.univ
      ((quotientScalarPerfectFunctor φ D S).obj
        ((triaToPerfect A (QuotientObject D S)).obj X)).obj :=
  exactPerfectFunctor_tria A (QuotientObject D S) _ (quotientScalarPerfectFunctor φ D S)
    (fun z => (derivedFiniteCellOver A' _ Set.univ).prop_of_iso
      (quotientScalarRepresentableIso φ S z).symm
      (triaRepresentable A' (QuotientObject (ScalarExtension.DGBaseChange φ D) S)
        ⟨z.val⟩).property) X

/-- 明示的 dg 商の tria 上での、実際の導来係数変更の制限。 -/
def quotientScalarTriaFunctor : TriaCategory A (QuotientObject D S) ⥤
    TriaCategory A' (QuotientObject (ScalarExtension.DGBaseChange φ D) S) :=
  (derivedFiniteCellOver A' _ Set.univ).lift
    (triaToPerfect A (QuotientObject D S) ⋙ quotientScalarPerfectFunctor φ D S ⋙
      (modulePerfect A' _).ι) (quotientScalarPerfect_tria φ S)

instance quotientScalarTriaFunctorCommShift : (quotientScalarTriaFunctor φ S).CommShift ℤ := by
  dsimp [quotientScalarTriaFunctor]
  infer_instance

instance quotientScalarTriaFunctorIsTriangulated :
    (quotientScalarTriaFunctor φ S).IsTriangulated := by
  dsimp [quotientScalarTriaFunctor]
  infer_instance

/-- tria への制限は、retract を加える Perf への包含と可換する。 -/
def quotientScalarTriaPerfectSquare :
    quotientScalarTriaFunctor φ S ⋙
        triaToPerfect A' (QuotientObject (ScalarExtension.DGBaseChange φ D) S) ≅
      triaToPerfect A (QuotientObject D S) ⋙ quotientScalarPerfectFunctor φ D S :=
  Iso.refl _

/-- tria の比較の全辺を忘れると U12f・U15d の実際の導来関手となる。 -/
def quotientScalarTriaInclusionIso :
    quotientScalarTriaFunctor φ S ⋙
        triaInclusion A' (QuotientObject (ScalarExtension.DGBaseChange φ D) S) ≅
      triaInclusion A (QuotientObject D S) ⋙
        ScalarExtension.derivedExtension φ (QuotientObject D S) ⋙
          dgDerivedExtension A' (ScalarExtension.DGBaseChange φ (QuotientObject D S))
            (QuotientObject (ScalarExtension.DGBaseChange φ D) S)
            (quotientBaseChangeDGFunctor φ D S) := Iso.refl _

variable (h : localKFlat A D S) (h' : localKFlat A' (ScalarExtension.DGBaseChange φ D) S)

/-- 未完備の指定 Verdier 商上へ、局所比較に沿って運んだ係数変更。 -/
def localScalarTriaExtension : TriaQuotient A D S ⥤
    TriaQuotient A' (ScalarExtension.DGBaseChange φ D) S :=
  (localQuotientTriaEquivalence A D S h).functor ⋙ quotientScalarTriaFunctor φ S ⋙
    (localQuotientTriaEquivalence A' (ScalarExtension.DGBaseChange φ D) S h').inverse

instance localScalarTriaExtensionCommShift : (localScalarTriaExtension φ S h h').CommShift ℤ := by
  dsimp [localScalarTriaExtension]
  infer_instance

instance localScalarTriaExtensionIsTriangulated :
    (localScalarTriaExtension φ S h h').IsTriangulated := by
  dsimp [localScalarTriaExtension]
  infer_instance

def localScalarTriaSquare :
    localScalarTriaExtension φ S h h' ⋙
        (localQuotientTriaEquivalence A' (ScalarExtension.DGBaseChange φ D) S h').functor ≅
      (localQuotientTriaEquivalence A D S h).functor ⋙ quotientScalarTriaFunctor φ S :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (localQuotientTriaEquivalence A'
        (ScalarExtension.DGBaseChange φ D) S h').counitIso ≪≫ Functor.rightUnitor _)

instance localScalarTriaSquareCommShift :
    NatTrans.CommShift (localScalarTriaSquare φ S h h').hom ℤ := by
  dsimp only [localScalarTriaSquare, Iso.trans_hom, isoWhiskerLeft_hom]
  infer_instance

/-- 既存の指定 `quotientVerdierComparison` そのものに対する係数変更正方形。 -/
def canonicalScalarTriaSquare :
    localScalarTriaExtension φ S h h' ⋙
        quotientVerdierComparison A' (ScalarExtension.DGBaseChange φ D) S ≅
      quotientVerdierComparison A D S ⋙ quotientScalarTriaFunctor φ S :=
  isoWhiskerLeft _ (quotientComparisonModelsIso A' (ScalarExtension.DGBaseChange φ D) S).symm ≪≫
    localScalarTriaSquare φ S h h' ≪≫
      isoWhiskerRight (quotientComparisonModelsIso A D S) _

def localScalarTriaSquareTriangle := Functor.mapTriangleIso (localScalarTriaSquare φ S h h')
end DGQuotient
end SerrePositivity.DifferentialGraded
end

end ScalarExtensionTria

/-! ## ScalarSourceVerdier（旧 SerrePositivity/DifferentialGraded/Verdier/ScalarSourceVerdier.lean） -/

/-! # 元の tria 上の係数変更から直接誘導する Verdier 関手

商との局所同値による輸送に先立ち、元の実際の係数変更を局所化する。
-/

@[expose] public section ScalarSourceVerdier
universe u v

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全 Perf 上の既存の主導来係数変更。生成集合の型を明示して固定する。 -/
def sourceScalarPerfectFunctor :
    PerfectModuleCategory A D ⥤ PerfectModuleCategory A' (ScalarExtension.DGBaseChange φ D) :=
  perfectScalarDerivedExtension φ D Set.univ

instance sourceScalarPerfectFunctorCommShift : (sourceScalarPerfectFunctor φ D).CommShift ℤ :=
  perfectScalarDerivedExtensionCommShift φ D Set.univ
instance sourceScalarPerfectFunctorIsTriangulated :
    (sourceScalarPerfectFunctor φ D).IsTriangulated :=
  perfectScalarDerivedExtensionIsTriangulated φ D Set.univ

/-- 係数変更した実際の代表加群の導来計算。同じ対象を生成元に取る。 -/
def sourceScalarRepresentableIso (d : D) :
    (ScalarExtension.derivedExtension φ D).obj (triaRepresentable A D d).obj ≅
      (triaRepresentable A' (ScalarExtension.DGBaseChange φ D) d).obj := by
  let M := ForgetEnrichment.of (Complex A) (representable A d)
  let e : (ScalarExtension.moduleExtension φ D).obj M ≅
      ForgetEnrichment.of (Complex A')
        (representable A' (show ScalarExtension.DGBaseChange φ D from d)) :=
    eqToIso (by
      change ForgetEnrichment.of (Complex A')
        (ScalarExtension.rightModule φ D (representable A d)) = _
      rw [scalarRepresentable_eq])
  exact scalarDerivedProjectiveComputation φ D M (representable_homotopicallyProjective A D d) ≪≫
    (moduleToDerived A' (ScalarExtension.DGBaseChange φ D)).mapIso e

lemma sourceScalarTria_mem (X : TriaCategory A D) :
    derivedFiniteCellOver A' (ScalarExtension.DGBaseChange φ D) Set.univ
      ((ScalarExtension.derivedExtension φ D).obj X.obj) :=
  exactPerfectFunctor_tria A D (ScalarExtension.DGBaseChange φ D)
    (sourceScalarPerfectFunctor φ D)
    (fun d => (derivedFiniteCellOver A' (ScalarExtension.DGBaseChange φ D) Set.univ).prop_of_iso
      (sourceScalarRepresentableIso φ D d).symm
      (triaRepresentable A' (ScalarExtension.DGBaseChange φ D) d).property) X

/-- 元の dg 圏の実際の導来係数変更を tria に制限する。 -/
def sourceScalarTriaFunctor :
    TriaCategory A D ⥤ TriaCategory A' (ScalarExtension.DGBaseChange φ D) :=
  (derivedFiniteCellOver A' _ Set.univ).lift
    (triaToPerfect A D ⋙ sourceScalarPerfectFunctor φ D ⋙ (modulePerfect A' _).ι)
    (sourceScalarTria_mem φ D)

instance sourceScalarTriaFunctorCommShift : (sourceScalarTriaFunctor φ D).CommShift ℤ := by
  dsimp [sourceScalarTriaFunctor]
  infer_instance
instance sourceScalarTriaFunctorIsTriangulated : (sourceScalarTriaFunctor φ D).IsTriangulated := by
  dsimp [sourceScalarTriaFunctor]
  infer_instance

/-- 制限を忘れると、元の主導来係数変更そのものに戻る。 -/
def sourceScalarTriaInclusionIso :
    sourceScalarTriaFunctor φ D ⋙ triaInclusion A' (ScalarExtension.DGBaseChange φ D) ≅
      triaInclusion A D ⋙ ScalarExtension.derivedExtension φ D := Iso.refl _

variable (S : Set D)

lemma sourceScalarTriaFunctor_image {X : TriaCategory A D} (hX : triaImage A D S X) :
    triaImage A' (ScalarExtension.DGBaseChange φ D) S ((sourceScalarTriaFunctor φ D).obj X) := by
  let P := (triaImage A' (ScalarExtension.DGBaseChange φ D) S).inverseImage
    (sourceScalarTriaFunctor φ D)
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  apply ((triaImage_le_iff_generators A D S P).2 ?_) X hX
  intro d hd
  exact (derivedFiniteCellOver A' (ScalarExtension.DGBaseChange φ D) S).prop_of_iso
    (sourceScalarRepresentableIso φ D d).symm
    (triaImage_representable A' (ScalarExtension.DGBaseChange φ D) S d hd)

lemma sourceScalarTriaFunctor_verdier_inverts :
    (triaImage A D S).trW.IsInvertedBy
      (sourceScalarTriaFunctor φ D ⋙ triaQuotient A' (ScalarExtension.DGBaseChange φ D) S) := by
  intro X Y f hf
  exact (triangulatedKernel_trW_iff _ f).1
    ((triaImage A D S).trW_monotone (fun X hX =>
      verdierQuotient_isZero (triaImage A' (ScalarExtension.DGBaseChange φ D) S) _
        (sourceScalarTriaFunctor_image φ D S hX)) _ hf)

/-- 局所 K-flat 条件を使わず、元の係数変更を先に Verdier 局所化した関手。 -/
def sourceScalarVerdierFunctor :
    TriaQuotient A D S ⥤ TriaQuotient A' (ScalarExtension.DGBaseChange φ D) S :=
  Localization.lift
    (sourceScalarTriaFunctor φ D ⋙ triaQuotient A' (ScalarExtension.DGBaseChange φ D) S)
    (sourceScalarTriaFunctor_verdier_inverts φ D S) (triaQuotient A D S)

def sourceScalarVerdierFactors :
    triaQuotient A D S ⋙ sourceScalarVerdierFunctor φ D S ≅
      sourceScalarTriaFunctor φ D ⋙ triaQuotient A' (ScalarExtension.DGBaseChange φ D) S :=
  Localization.fac _ (sourceScalarTriaFunctor_verdier_inverts φ D S) _

instance sourceScalarVerdierLifting :
    Localization.Lifting (triaQuotient A D S) (triaImage A D S).trW
      (sourceScalarTriaFunctor φ D ⋙ triaQuotient A' (ScalarExtension.DGBaseChange φ D) S)
      (sourceScalarVerdierFunctor φ D S) :=
  Localization.liftingLift _ (sourceScalarTriaFunctor_verdier_inverts φ D S) _

instance sourceScalarVerdierFunctorCommShift : (sourceScalarVerdierFunctor φ D S).CommShift ℤ :=
  Functor.commShiftOfLocalization (triaQuotient A D S) (triaImage A D S).trW ℤ
    (sourceScalarTriaFunctor φ D ⋙ triaQuotient A' (ScalarExtension.DGBaseChange φ D) S)
    (sourceScalarVerdierFunctor φ D S)
instance sourceScalarVerdierFactorsCommShift :
    NatTrans.CommShift (sourceScalarVerdierFactors φ D S).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization (triaQuotient A D S) (triaImage A D S).trW ℤ
    (sourceScalarTriaFunctor φ D ⋙ triaQuotient A' (ScalarExtension.DGBaseChange φ D) S)
    (sourceScalarVerdierFunctor φ D S)
instance sourceScalarVerdierFunctorIsTriangulated :
    (sourceScalarVerdierFunctor φ D S).IsTriangulated := by
  have : (triaQuotient A D S).mapArrow.EssSurj :=
    Localization.essSurj_mapArrow (triaQuotient A D S) (triaImage A D S).trW
  exact Functor.isTriangulated_of_precomp_iso (sourceScalarVerdierFactors φ D S)

def sourceScalarVerdierFactorsTriangle := Functor.mapTriangleIso (sourceScalarVerdierFactors φ D S)
end SerrePositivity.DifferentialGraded
end

end ScalarSourceVerdier

/-! ## ScalarGraphDerivedComparison（旧 SerrePositivity/DifferentialGraded/Verdier/ScalarGraphDerivedComparison.lean） -/

/-! # 実際の導来係数変更と graph 延長の perfect 始域上の交換

通常の交換同型と射影的モデルでの計算を使い、所望の導来正方形を仮定しない。
-/

@[expose] public section ScalarGraphDerivedComparison
universe u v w

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

section Computations
variable {C : Type*} [Category* C] (I : C ⥤ ModuleCategory A D)
  (hI : ∀ X, moduleHomotopicallyProjective A D (I.obj X))

/-- 射影的モデルの族に制限した、既存の graph 導来計算の自然同型。 -/
def graphProjectiveFamilyComputation :
    I ⋙ moduleToDerived A D ⋙ dgDerivedExtension A D E F ≅
      I ⋙ (dgModuleExtension A D E F).onClosed ⋙ moduleToDerived A E := by
  let τ := whiskerLeft I (DGQuotient.derivedExtensionUnderivedNatTrans A D E F)
  let : ∀ X, IsIso (τ.app X) := fun X =>
    DGQuotient.derivedExtensionUnderivedMap_isIso A D E F (I.obj X) (hI X)
  let := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- 射影的モデルの族に制限した、既存の係数変更の導来計算の自然同型。 -/
def scalarProjectiveFamilyComputation :
    I ⋙ moduleToDerived A D ⋙ ScalarExtension.derivedExtension φ D ≅
      I ⋙ ScalarExtension.moduleExtension φ D ⋙
        moduleToDerived A' (ScalarExtension.DGBaseChange φ D) := by
  let τ := whiskerLeft I (ScalarExtension.derivedExtensionAugmentation φ D)
  let : ∀ X, IsIso (τ.app X) := fun X =>
    scalarDerivedExtensionAugmentation_isIso_of_projective φ D (I.obj X) (hI X)
  let := NatIso.isIso_of_isIso_app τ
  exact asIso τ
end Computations

/-- 射影的 perfect 代表から全加群への実際の閉零包含。 -/
abbrev scalarGraphPerfectClosedInclusion := (perfectDGModuleInclusion A D Set.univ).onClosed

/-- 閉零射影的 perfect 代表上で、二つの実際の導来複合関手を比較する。 -/
def scalarGraphPerfectClosedSquare :
    scalarGraphPerfectClosedInclusion (A := A) D ⋙ moduleToDerived A D ⋙
        dgDerivedExtension A D E F ⋙ ScalarExtension.derivedExtension φ E ≅
      scalarGraphPerfectClosedInclusion (A := A) D ⋙ moduleToDerived A D ⋙
        ScalarExtension.derivedExtension φ D ⋙
          dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D)
            (ScalarExtension.DGBaseChange φ E)
            (ScalarExtension.dgFunctor φ F) := by
  let I := scalarGraphPerfectClosedInclusion (A := A) D
  have hI : ∀ X, moduleHomotopicallyProjective A D (I.obj X) := fun X =>
    (ForgetEnrichment.to (Complex A) X).property.1
  let J := I ⋙ (dgModuleExtension A D E F).onClosed
  have hJ : ∀ X, moduleHomotopicallyProjective A E (J.obj X) := fun X =>
    dgModuleExtension_homotopicallyProjective A D E F (hI X)
  let I' := I ⋙ ScalarExtension.moduleExtension φ D
  have hI' : ∀ X, moduleHomotopicallyProjective A' (ScalarExtension.DGBaseChange φ D) (I'.obj X) :=
    fun X => scalarModuleExtension_projective_perfect φ D
      (ForgetEnrichment.to (Complex A) X).property.1
      (ForgetEnrichment.to (Complex A) X).property.2
  exact
    isoWhiskerRight (graphProjectiveFamilyComputation (A := A) D E F I hI)
      (ScalarExtension.derivedExtension φ E) ≪≫
    scalarProjectiveFamilyComputation φ E J hJ ≪≫
    isoWhiskerLeft I (isoWhiskerRight (scalarGraphExtensionIso φ D E F)
      (moduleToDerived A' (ScalarExtension.DGBaseChange φ E))) ≪≫
    (graphProjectiveFamilyComputation (A := A') (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.DGBaseChange φ E) (ScalarExtension.dgFunctor φ F) I' hI').symm ≪≫
    isoWhiskerRight (scalarProjectiveFamilyComputation φ D I hI).symm
      (dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D) (ScalarExtension.DGBaseChange φ E)
        (ScalarExtension.dgFunctor φ F))

/-- 閉零代表から H⁰ への商の充満性によって比較を降ろす。 -/
def scalarGraphPerfectHomotopySquare :
    perfectDGModuleToDerived A D Set.univ ⋙
        dgDerivedExtension A D E F ⋙ ScalarExtension.derivedExtension φ E ≅
      perfectDGModuleToDerived A D Set.univ ⋙ ScalarExtension.derivedExtension φ D ⋙
        dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D) (ScalarExtension.DGBaseChange φ E)
          (ScalarExtension.dgFunctor φ F) :=
  Quotient.natIsoLift (boundaryRelation A (PerfectDGModuleOver A D Set.univ))
    ((associator _ _ _).symm ≪≫
      isoWhiskerRight (perfectDGModuleClosedToDerivedIso A D Set.univ)
        (dgDerivedExtension A D E F ⋙ ScalarExtension.derivedExtension φ E) ≪≫
      scalarGraphPerfectClosedSquare φ D E F ≪≫
      isoWhiskerRight (perfectDGModuleClosedToDerivedIso A D Set.univ).symm
        (ScalarExtension.derivedExtension φ D ⋙
          dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D)
            (ScalarExtension.DGBaseChange φ E)
            (ScalarExtension.dgFunctor φ F)) ≪≫ associator _ _ _)

/-- 元の Perf の包含上の、係数変更と graph 延長の実際の導来正方形。 -/
def scalarGraphPerfectDerivedSquare :
    (modulePerfect A D).ι ⋙ dgDerivedExtension A D E F ⋙ ScalarExtension.derivedExtension φ E ≅
      (modulePerfect A D).ι ⋙ ScalarExtension.derivedExtension φ D ⋙
        dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D) (ScalarExtension.DGBaseChange φ E)
          (ScalarExtension.dgFunctor φ F) := by
  let e := perfectDGModuleHomotopyEquivalence A D Set.univ
  let L := dgDerivedExtension A D E F ⋙ ScalarExtension.derivedExtension φ E
  let R := ScalarExtension.derivedExtension φ D ⋙
    dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D) (ScalarExtension.DGBaseChange φ E)
      (ScalarExtension.dgFunctor φ F)
  exact
    isoWhiskerRight e.counitIso.symm ((modulePerfect A D).ι ⋙ L) ≪≫
    isoWhiskerLeft e.inverse (scalarGraphPerfectHomotopySquare φ D E F) ≪≫
    isoWhiskerRight e.counitIso ((modulePerfect A D).ι ⋙ R)
end SerrePositivity.DifferentialGraded
end

end ScalarGraphDerivedComparison

/-! ## ScalarQuotientSourceSquare（旧 SerrePositivity/DifferentialGraded/Verdier/ScalarQuotientSourceSquare.lean） -/

/-! # 元の tria からの係数変更と明示的 dg 商の比較

通常の交換、射影的 perfect モデル、固定 path の包含等式から構成する。
-/

@[expose] public section ScalarQuotientSourceSquare
universe u v

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory CategoryTheory.Functor
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D] (S : Set D)

/-- 係数変更の前後で明示的 dg 商への実際の導来延長を行う正方形。 -/
def sourceScalarQuotientDerivedSquare :
    triaInclusion A D ⋙ dgDerivedExtension A D (QuotientObject D S) (inclusion A D S) ⋙
        ScalarExtension.derivedExtension φ (QuotientObject D S) ⋙
          dgDerivedExtension A' (ScalarExtension.DGBaseChange φ (QuotientObject D S))
            (QuotientObject (ScalarExtension.DGBaseChange φ D) S)
            (quotientBaseChangeDGFunctor φ D S) ≅
      triaInclusion A D ⋙ ScalarExtension.derivedExtension φ D ⋙
        dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D)
          (QuotientObject (ScalarExtension.DGBaseChange φ D) S)
          (inclusion A' (ScalarExtension.DGBaseChange φ D) S) := by
  let e : triaInclusion A D ⋙
      dgDerivedExtension A D (QuotientObject D S) (inclusion A D S) ⋙
        ScalarExtension.derivedExtension φ (QuotientObject D S) ≅
      triaInclusion A D ⋙ ScalarExtension.derivedExtension φ D ⋙
        dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D)
          (ScalarExtension.DGBaseChange φ (QuotientObject D S))
          (ScalarExtension.dgFunctor φ (inclusion A D S)) :=
    isoWhiskerLeft (triaToPerfect A D)
      (scalarGraphPerfectDerivedSquare φ D (QuotientObject D S) (inclusion A D S))
  exact isoWhiskerRight e
      (dgDerivedExtension A' (ScalarExtension.DGBaseChange φ (QuotientObject D S))
        (QuotientObject (ScalarExtension.DGBaseChange φ D) S)
        (quotientBaseChangeDGFunctor φ D S)) ≪≫
    isoWhiskerLeft (triaInclusion A D ⋙ ScalarExtension.derivedExtension φ D)
      (derivedGraphExtensionCompositionIso A' (ScalarExtension.DGBaseChange φ D)
        (ScalarExtension.DGBaseChange φ (QuotientObject D S))
        (QuotientObject (ScalarExtension.DGBaseChange φ D) S)
        (ScalarExtension.dgFunctor φ (inclusion A D S)) (quotientBaseChangeDGFunctor φ D S) ≪≫
        eqToIso (congrArg
          (dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D)
            (QuotientObject (ScalarExtension.DGBaseChange φ D) S))
          (quotientBaseChangeDGFunctor_inclusion φ D S)))

/-- 上の同型を商側の tria に制限した実際の正方形。 -/
def sourceScalarQuotientTriaSquare :
    derivedComparisonTria A D S ⋙ quotientScalarTriaFunctor φ S ≅
      sourceScalarTriaFunctor φ D ⋙
        derivedComparisonTria A' (ScalarExtension.DGBaseChange φ D) S :=
  ((whiskeringRight _ _ _).obj
    (triaInclusion A' (QuotientObject (ScalarExtension.DGBaseChange φ D) S))).preimageIso
    (sourceScalarQuotientDerivedSquare φ D S)

/-- 元の係数変更を先に局所化した関手と、局所商比較との正方形。 -/
def sourceScalarLocalQuotientSquare :
    sourceScalarVerdierFunctor φ D S ⋙
        localQuotientTriaFunctor A' (ScalarExtension.DGBaseChange φ D) S ≅
      localQuotientTriaFunctor A D S ⋙ quotientScalarTriaFunctor φ S :=
  (Localization.fullyFaithfulWhiskeringLeft
    (triaQuotient A D S) (triaImage A D S).trW _).preimageIso
    ((associator _ _ _).symm ≪≫
      isoWhiskerRight (sourceScalarVerdierFactors φ D S) _ ≪≫
      associator _ _ _ ≪≫
      isoWhiskerLeft (sourceScalarTriaFunctor φ D)
        (localQuotientTriaFactors A' (ScalarExtension.DGBaseChange φ D) S) ≪≫
      (sourceScalarQuotientTriaSquare φ D S).symm ≪≫
      isoWhiskerRight (localQuotientTriaFactors A D S).symm _ ≪≫ associator _ _ _)

variable (h : localKFlat A D S) (h' : localKFlat A' (ScalarExtension.DGBaseChange φ D) S)

/-- 直接局所化した元の係数変更と、以前の局所同値による輸送は自然同型になる。 -/
def sourceScalarLocalTransportIso :
    sourceScalarVerdierFunctor φ D S ≅ localScalarTriaExtension φ S h h' :=
  ((whiskeringRight _ _ _).obj
    (localQuotientTriaEquivalence A' (ScalarExtension.DGBaseChange φ D) S h').functor).preimageIso
    (sourceScalarLocalQuotientSquare φ D S ≪≫ (localScalarTriaSquare φ S h h').symm)

/-- 直接局所化した係数変更に対する、既存の指定 Verdier 比較そのものの正方形。 -/
def sourceScalarCanonicalQuotientSquare :
    sourceScalarVerdierFunctor φ D S ⋙
        quotientVerdierComparison A' (ScalarExtension.DGBaseChange φ D) S ≅
      quotientVerdierComparison A D S ⋙ quotientScalarTriaFunctor φ S :=
  isoWhiskerLeft _ (quotientComparisonModelsIso A' (ScalarExtension.DGBaseChange φ D) S).symm ≪≫
    sourceScalarLocalQuotientSquare φ D S ≪≫
      isoWhiskerRight (quotientComparisonModelsIso A D S) _
end SerrePositivity.DifferentialGraded.DGQuotient
end

end ScalarQuotientSourceSquare
