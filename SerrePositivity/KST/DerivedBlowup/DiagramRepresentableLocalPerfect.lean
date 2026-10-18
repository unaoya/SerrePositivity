module

public import SerrePositivity.KST.DerivedBlowup.DiagramRepresentableLocalRegular
public import SerrePositivity.DifferentialGraded.Perfect.Basic

/-!
概要：KST §3.1 の包含先に制限した共変 representable の局所 perfect 性。
方針：指定 regular 比較の擬同型を主導来局所化で反転し、代表生成元の perfect 性を移す。
規約：大域係数圏の small 仮定を追加せず、局所一対象圏で導来化する。
使われ方：構造図式加群の局所 perfect 性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：包含先での指定局所 regular 比較は objectwise 擬同型。
方針：一対象での成分を Hom の標準同定射へ戻す。
規約：KST §3.1。使われ方：主導来圏での局所 regular 比較同型。 -/
theorem diagramRepresentableLocalRegularMap_quasiIso {i j : J} (h : i ≤ j) :
    moduleQuasiIso R (AlgebraVertex (F.obj j))ᵒᵖ
      (diagramRepresentableLocalRegularMap F h) := by
  intro x
  cases x using Opposite.rec
  rename_i x
  cases x
  rw [diagramRepresentableLocalRegularMap_eval]
  unfold diagramModuleHomInclusion
  infer_instance

/-- 概要：制限 representable の主導来像は局所 regular 代表加群の主導来像と同型。
方針：構成済み指定擬同型を主局所化で反転する。
規約：KST §3.1。使われ方：構造加群と局所自由生成元の比較。 -/
def diagramRepresentableLocalRegularDerivedIso {i j : J} (h : i ≤ j) :
    (moduleToDerived R (AlgebraVertex (F.obj j))ᵒᵖ).obj
      (ForgetEnrichment.of (Complex R) (representable R (op (.point : AlgebraVertex (F.obj j))))) ≅
    (moduleToDerived R (AlgebraVertex (F.obj j))ᵒᵖ).obj
      (ForgetEnrichment.of (Complex R) (diagramRepresentableLocalRaw F i j)) :=
  moduleDerivedIso R (AlgebraVertex (F.obj j))ᵒᵖ (diagramRepresentableLocalRegularMap F h)
    (diagramRepresentableLocalRegularMap_quasiIso F h)

/-- 概要：包含先に制限した共変 representable は局所で perfect。
方針：局所代表生成元の perfect 性を指定導来同型に沿って移す。
規約：KST §3.1。使われ方：構造図式加群の各頂点の perfect 性。 -/
theorem diagramRepresentableLocalRaw_perfect {i j : J} (h : i ≤ j) :
    modulePerfect R (AlgebraVertex (F.obj j))ᵒᵖ
      ((moduleToDerived R (AlgebraVertex (F.obj j))ᵒᵖ).obj
        (ForgetEnrichment.of (Complex R) (diagramRepresentableLocalRaw F i j))) :=
  (modulePerfect R (AlgebraVertex (F.obj j))ᵒᵖ).prop_of_iso
    (diagramRepresentableLocalRegularDerivedIso F h)
    (modulePerfectOver_representable R (AlgebraVertex (F.obj j))ᵒᵖ
      (op .point) (Set.mem_univ _))

end SerrePositivity.KST.DerivedBlowup
