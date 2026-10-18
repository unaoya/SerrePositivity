module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeModuleExtensionIso
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionAdjunction
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
概要：KST §3.1 の graph 重み付けを局所係数制限の指定同型へ随伴で移す。
方針：指定延長–制限随伴で自然自己同型の mate を取り、単位挿入と評価で計算する。
規約：graph の重みは次数零の単位への作用として表す。
使われ方：任意の図式加群の指定遷移に現れる捻りの比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)

/-- 概要：graph 重みの通常延長自己同型を随伴で移した局所制限の指定自己同型。
方針：同じ指定随伴の間の conjugateIsoEquiv を使う。
規約：KST §3.1。使われ方：捻りの局所制限比較の可逆な重み。 -/
def diagramGaugeModuleRestrictionIso {i j : J} (h : i ≤ j) :
    moduleRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
        (diagramAlgebraVertexTransition F h).op.op ≅
      moduleRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
        (diagramAlgebraVertexTransition F h).op.op :=
  let A := dgModuleExtensionRestrictionAdjunction R
    (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
    (diagramAlgebraVertexTransition F h).op
  conjugateIsoEquiv A A (diagramGaugeModuleExtensionIso F s h)

/-- 概要：指定制限自己同型の成分は単位・graph 重み・余単位の指定合成。
方針：mate の成分公式を指定延長–制限随伴へ適用する。
規約：KST §3.1。使われ方：局所単位への重みの作用の計算。 -/
theorem diagramGaugeModuleRestrictionIso_hom_app {i j : J} (h : i ≤ j)
    (M : ModuleCategory R (AlgebraVertex (F.obj j))ᵒᵖ) :
    (diagramGaugeModuleRestrictionIso F s h).hom.app M =
      (dgModuleUnit R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
        (diagramAlgebraVertexTransition F h).op).app
          ((moduleRestriction R _ _ (diagramAlgebraVertexTransition F h).op.op).obj M) ≫
      (moduleRestriction R _ _ (diagramAlgebraVertexTransition F h).op.op).map
        ((diagramGaugeModuleExtensionIso F s h).hom.app
          ((moduleRestriction R _ _ (diagramAlgebraVertexTransition F h).op.op).obj M)) ≫
      (moduleRestriction R _ _ (diagramAlgebraVertexTransition F h).op.op).map
        ((dgModuleCounit R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
          (diagramAlgebraVertexTransition F h).op).app M) := by
  unfold diagramGaugeModuleRestrictionIso
  rw [conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app]
  rfl

end SerrePositivity.KST.DerivedBlowup
