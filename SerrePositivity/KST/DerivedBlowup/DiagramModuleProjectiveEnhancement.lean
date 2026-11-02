module

public import SerrePositivity.KST.DerivedBlowup.DiagramModuleProjectiveResolution
public import SerrePositivity.DifferentialGraded.Derived.Projective

/-!
概要：KST §3.1 の全 diagram-module の射影的 dg 模型と主導来圏の H⁰ 比較。
方針：全次数 Hom に対する射影性で局所化 Hom を計算し、標準半自由分解で本質的全射性を示す。
規約：cartesian・perfect 条件や層の降下比較とは区別する。
使われ方：mapping 複体も導来化する全 diagram-module 模型の検証。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：射影的 diagram-module から全 dg 加群への充満 dg 包含。
方針：既存の充満 dg 部分圏の包含を使う。
規約：KST §3.1、全次数の Hom を保つ。
使われ方：主導来局所化への比較を作る。 -/
def projectiveDiagramModuleInclusion :
    DGFunctor R (ProjectiveDiagramModules F)
      (RightModule R (DiagramModuleCoefficientObject F)ᵒᵖ) :=
  dgFullSubcategoryInclusion R _ (projectiveDiagramModuleProperty F)

/-- 概要：射影的 diagram-module の H⁰ 包含は充満。
方針：充満 dg 部分圏の一般定理を適用する。
規約：KST §3.1。使われ方：主導来比較の充満性。 -/
instance projectiveDiagramModuleInclusionHomotopyFull :
    (projectiveDiagramModuleInclusion F).onHomotopy.Full := by
  dsimp [projectiveDiagramModuleInclusion]
  infer_instance

/-- 概要：射影的 diagram-module の H⁰ 包含は忠実。
方針：元の Hom と境界関係を保つ一般定理を適用する。
規約：KST §3.1。使われ方：主導来比較の忠実性。 -/
instance projectiveDiagramModuleInclusionHomotopyFaithful :
    (projectiveDiagramModuleInclusion F).onHomotopy.Faithful := by
  dsimp [projectiveDiagramModuleInclusion]
  infer_instance

/-- 概要：射影的 dg 模型の実際の H⁰ から全 diagram-module の主導来圏への比較。
方針：充満 dg 包含の H⁰ と既存の局所化関手を合成する。
規約：KST §3.1。使われ方：全図式の導来 mapping 計算の比較。 -/
def projectiveDiagramModuleToDerived :
    HomotopyCategory R (ProjectiveDiagramModules F) ⥤ DerivedAllDiagramModules F :=
  (projectiveDiagramModuleInclusion F).onHomotopy ⋙
    moduleHomotopyToDerivedClosed R (DiagramModuleCoefficientObject F)ᵒᵖ

/-- 概要：射影的図式模型から主導来圏への比較は充満。
方針：始域の全 Hom 射影性による局所化 Hom 計算を H⁰ 包含の充満性へ接続する。
規約：KST §3.1。使われ方：導来比較の完全忠実性。 -/
instance projectiveDiagramModuleToDerivedFull : (projectiveDiagramModuleToDerived F).Full where
  map_surjective {X Y} f := by
    let M : ProjectiveDiagramModules F := ForgetEnrichment.to (Complex R) X.as
    let N : AllDiagramModules F := ForgetEnrichment.of (Complex R) M.val
    obtain ⟨g, hg⟩ := (moduleProjectiveLocalization_map_bijective R
      (DiagramModuleCoefficientObject F)ᵒᵖ (P := N) M.property
      ((projectiveDiagramModuleInclusion F).onHomotopy.obj Y)).2 f
    obtain ⟨h, hh⟩ := (projectiveDiagramModuleInclusion F).onHomotopy.map_surjective g
    refine ⟨h, ?_⟩
    change (moduleHomotopyToDerivedClosed R (DiagramModuleCoefficientObject F)ᵒᵖ).map
      ((projectiveDiagramModuleInclusion F).onHomotopy.map h) = f
    rw [hh]
    exact hg

/-- 概要：射影的図式模型から主導来圏への比較は忠実。
方針：射影的始域の局所化 Hom 写像の単射性を使う。
規約：KST §3.1。使われ方：導来比較の完全忠実性。 -/
instance projectiveDiagramModuleToDerivedFaithful :
    (projectiveDiagramModuleToDerived F).Faithful where
  map_injective {X Y} f g h := by
    let M : ProjectiveDiagramModules F := ForgetEnrichment.to (Complex R) X.as
    let N : AllDiagramModules F := ForgetEnrichment.of (Complex R) M.val
    apply (projectiveDiagramModuleInclusion F).onHomotopy.map_injective
    exact (moduleProjectiveLocalization_map_bijective R (DiagramModuleCoefficientObject F)ᵒᵖ
      (P := N) M.property ((projectiveDiagramModuleInclusion F).onHomotopy.obj Y)).1 h

/-- 概要：標準半自由分解によって主導来圏の全対象を表せる。
方針：主局所化の対象を実際の図式加群に戻し、その標準分解の擬同型を使う。
規約：KST §3.1。使われ方：射影的 dg 模型の H⁰ 比較の本質的全射性。 -/
instance projectiveDiagramModuleToDerivedEssSurj :
    (projectiveDiagramModuleToDerived F).EssSurj where
  mem_essImage X := by
    let P := diagramModuleProjectiveResolution F X.as.obj
    let e : (moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ).obj P.obj ≅ X :=
      moduleDerivedIso R (DiagramModuleCoefficientObject F)ᵒᵖ P.π P.quasiIso
    let M := projectiveDiagramModuleRepresentative F X.as.obj
    refine ⟨(toHomotopy R (ProjectiveDiagramModules F)).obj
      (ForgetEnrichment.of (Complex R) M), ⟨?_⟩⟩
    exact (moduleToHomotopyDerivedIso R (DiagramModuleCoefficientObject F)ᵒᵖ).app P.obj ≪≫ e

/-- 概要：射影的 diagram-module の H⁰ 比較は同値。
方針：証明済みの充満・忠実・本質的全射性を束ねる。
規約：KST §3.1。使われ方：主導来圏の dg 模型の H⁰ 比較。 -/
instance projectiveDiagramModuleToDerivedIsEquivalence :
    (projectiveDiagramModuleToDerived F).IsEquivalence where

/-- 概要：全 diagram-module の射影的 dg 模型の H⁰ と主導来局所化の同値。
方針：構成済みの比較関手を同値として読む。
規約：KST §3.1、cartesian 条件の比較や dg 商との比較はまだ別に残す。
使われ方：coherent な降下模型の全図式での導来 mapping 計算の基礎。 -/
def projectiveDiagramModuleHomotopyEquivalence :
    HomotopyCategory R (ProjectiveDiagramModules F) ≌ DerivedAllDiagramModules F :=
  (projectiveDiagramModuleToDerived F).asEquivalence

end SerrePositivity.KST.DerivedBlowup
