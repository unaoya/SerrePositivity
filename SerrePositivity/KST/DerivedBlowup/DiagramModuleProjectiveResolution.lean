module

public import SerrePositivity.KST.DerivedBlowup.DiagramModuleCoefficientCategory
public import SerrePositivity.DifferentialGraded.Category.FullSubcategory
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveResolution

/-!
概要：KST §3.1 の全 diagram-module の図式全体での半自由・射影的置換。
方針：構成済みの係数 dg 圏に既存の標準半自由分解を適用する。
規約：各評価の射影性で代用せず、図式全体の全次数 Hom の射影性を使う。
使われ方：mapping 複体の導来化と coherent な降下模型の準備。
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

/-- 概要：全 diagram-module の標準の射影的分解。
方針：係数 dg 圏の opposite に既存の構成済み標準分解を適用する。
規約：KST §3.1、対象・増大射・射影性・擬同型の全てを保持する。
使われ方：図式全体での mapping 複体の計算。 -/
def diagramModuleProjectiveResolution (M : AllDiagramModules F) :
    ModuleProjectiveResolution R (DiagramModuleCoefficientObject F)ᵒᵖ M :=
  moduleCanonicalProjectiveResolution R (DiagramModuleCoefficientObject F)ᵒᵖ M

/-- 概要：標準図式分解は図式全体の半自由加群。
方針：既存の標準分解の半自由 filtration を使う。
規約：KST §3.1。使われ方：図式全体の Hom を導来化する置換の実体。 -/
theorem diagramModuleProjectiveResolution_semifree (M : AllDiagramModules F) :
    moduleSemifree R (DiagramModuleCoefficientObject F)ᵒᵖ
      (diagramModuleProjectiveResolution F M).obj :=
  moduleResolutionCandidate_semifree R (DiagramModuleCoefficientObject F)ᵒᵖ M

/-- 概要：標準図式分解の増大射は objectwise 擬同型。
方針：構成済み分解の擬同型証明を取り出す。
規約：KST §3.1。使われ方：全 diagram-module の導来局所化への接続。 -/
theorem diagramModuleProjectiveResolution_quasiIso (M : AllDiagramModules F) :
    moduleQuasiIso R (DiagramModuleCoefficientObject F)ᵒᵖ
      (diagramModuleProjectiveResolution F M).π :=
  (diagramModuleProjectiveResolution F M).quasiIso

/-- 概要：図式全体で homotopically projective な実際の dg 加群という性質。
方針：全次数 Hom end が objectwise acyclic を消す既存の性質を使う。
規約：KST §3.1。使われ方：導来 mapping 複体を計算する充満 dg 部分圏。 -/
def projectiveDiagramModuleProperty
    (M : RightModule R (DiagramModuleCoefficientObject F)ᵒᵖ) : Prop :=
  moduleHomotopicallyProjective R (DiagramModuleCoefficientObject F)ᵒᵖ
    (ForgetEnrichment.of (Complex R) M)

/-- 概要：全次数 Hom を保つ射影的 diagram-module の充満 dg 部分圏。
方針：既存の DGFullSubcategory で射影的加群に制限する。
規約：KST §3.1、最終的な cartesian・perfect 模型とはまだ区別する。
使われ方：図式全体の導来 mapping 複体の実際の dg 模型。 -/
abbrev ProjectiveDiagramModules :=
  DGFullSubcategory (RightModule R (DiagramModuleCoefficientObject F)ᵒᵖ)
    (projectiveDiagramModuleProperty F)

/-- 概要：任意の diagram-module の射影的 dg 代表。
方針：標準分解の実際の加群と証明済みの射影性を束ねる。
規約：KST §3.1。使われ方：充満 dg 部分圏に対象を持ち上げる。 -/
def projectiveDiagramModuleRepresentative (M : AllDiagramModules F) : ProjectiveDiagramModules F :=
  ⟨ForgetEnrichment.to (Complex R) (diagramModuleProjectiveResolution F M).obj,
    (diagramModuleProjectiveResolution F M).projective⟩

/-- 概要：射影的置換から objectwise acyclic への全次数 Hom は acyclic。
方針：図式全体に対する分解の射影性をそのまま適用する。
規約：KST §3.1。使われ方：mapping 複体の導来計算の検証。 -/
theorem diagramModuleResolutionHom_acyclic (M N : AllDiagramModules F)
    (hN : moduleAcyclic R (DiagramModuleCoefficientObject F)ᵒᵖ N) :
    (moduleHom R (DiagramModuleCoefficientObject F)ᵒᵖ
      (ForgetEnrichment.to (Complex R) (diagramModuleProjectiveResolution F M).obj)
      (ForgetEnrichment.to (Complex R) N)).Acyclic :=
  (diagramModuleProjectiveResolution F M).projective N hN

end SerrePositivity.KST.DerivedBlowup
