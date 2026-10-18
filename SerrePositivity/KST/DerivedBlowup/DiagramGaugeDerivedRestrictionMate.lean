module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeRestrictionMate
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedComparison
public import SerrePositivity.KST.DerivedBlowup.TransitionDerivedRestrictionCoherence

/-!
概要：KST §3.1 の制限側 gauge mate を主導来局所化へ送る。
方針：標準制限の因子分解で通常の mate を挟み、指定自然同型延長を使う。
規約：canonical な導来比較には既存の指定導来随伴を使う。
使われ方：一般対象の cartesian 性を捻りに沿って保存する比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Functor DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)

/-- 概要：制限側 mate の導来延長前の指定自然自己同型。
方針：通常制限の mate を局所化で送り、標準因子分解同型の順逆で挟む。
規約：KST §3.1。使われ方：導来制限自己同型の指定経路。 -/
def diagramGaugeDerivedRestrictionPreIso {i j : J} (h : i ≤ j) :
    moduleToDerived R (AlgebraVertex (F.obj j))ᵒᵖ ⋙ diagramAlgebraDerivedRestriction F h ≅
      moduleToDerived R (AlgebraVertex (F.obj j))ᵒᵖ ⋙ diagramAlgebraDerivedRestriction F h :=
  eqToIso (dgDerivedRestriction_fac R (AlgebraVertex (F.obj i))ᵒᵖ
      (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op) ≪≫
    isoWhiskerRight (diagramGaugeModuleRestrictionIso F s h)
      (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ) ≪≫
    (eqToIso (dgDerivedRestriction_fac R (AlgebraVertex (F.obj i))ᵒᵖ
      (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op)).symm

/-- 概要：通常制限の mate を指定局所化へ延長した導来制限自己同型。
方針：主局所化前の指定同型を全導来対象へ延長する。
規約：KST §3.1。使われ方：一般対象の指定導来制限比較の重み。 -/
def diagramGaugeDerivedRestrictionIso {i j : J} (h : i ≤ j) :
    diagramAlgebraDerivedRestriction F h ≅ diagramAlgebraDerivedRestriction F h :=
  moduleDerivedIsoExtension (diagramGaugeDerivedRestrictionPreIso F s h)

/-- 概要：導来制限 mate の実加群上の順成分は元の mate の主局所化像。
方針：指定延長の成分公式と標準因子分解の対象保持を使う。
規約：KST §3.1。使われ方：通常加群比較の可換式を導来化する。 -/
theorem diagramGaugeDerivedRestrictionIso_hom_app_Q {i j : J} (h : i ≤ j)
    (M : ModuleCategory R (AlgebraVertex (F.obj j))ᵒᵖ) :
    (diagramGaugeDerivedRestrictionIso F s h).hom.app
        ((moduleToDerived R (AlgebraVertex (F.obj j))ᵒᵖ).obj M) =
      (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
        ((diagramGaugeModuleRestrictionIso F s h).hom.app M) := by
  unfold diagramGaugeDerivedRestrictionIso
  rw [moduleDerivedIsoExtension_hom_app]
  rfl

/-- 概要：局所化した制限 mate を指定導来随伴で戻した係数拡大の指定自己同型。
方針：同じ指定導来随伴の間の conjugateIsoEquiv の逆を使う。
規約：KST §3.1、graph の直接の導来像との比較は独立した整合性命題。
使われ方：canonical な係数拡大比較の可逆な重み付け。 -/
def diagramGaugeDerivedExtensionMateIso {i j : J} (h : i ≤ j) :
    diagramAlgebraDerivedExtension F h ≅ diagramAlgebraDerivedExtension F h :=
  let A := dgDerivedExtensionRestrictionAdjunction R
    (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
    (diagramAlgebraVertexTransition F h).op
  (conjugateIsoEquiv A A).symm (diagramGaugeDerivedRestrictionIso F s h)

/-- 概要：指定係数拡大 mate の共役像は指定導来制限自己同型。
方針：同型の共役対応の逆元律を順射で評価する。
規約：KST §3.1。使われ方：指定随伴の単位を通して比較経路を移す。 -/
theorem diagramGaugeDerivedExtensionMateIso_conjugate {i j : J} (h : i ≤ j) :
    conjugateEquiv
        (dgDerivedExtensionRestrictionAdjunction R
          (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
          (diagramAlgebraVertexTransition F h).op)
        (dgDerivedExtensionRestrictionAdjunction R
          (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
          (diagramAlgebraVertexTransition F h).op)
        (diagramGaugeDerivedExtensionMateIso F s h).hom =
      (diagramGaugeDerivedRestrictionIso F s h).hom := by
  let A := dgDerivedExtensionRestrictionAdjunction R
    (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
    (diagramAlgebraVertexTransition F h).op
  exact congrArg Iso.hom ((conjugateIsoEquiv A A).apply_symm_apply
    (diagramGaugeDerivedRestrictionIso F s h))

end SerrePositivity.KST.DerivedBlowup
