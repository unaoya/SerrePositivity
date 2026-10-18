module

public import SerrePositivity.KST.DerivedBlowup.DiagramStructureUnitTransition

/-!
概要：KST §3.1 の構造加群の局所 regular 比較と指定加群遷移の可換式。
方針：閉零 Yoneda 拡張の後合成・制限自然性と単位生成元の遷移公式を使う。
規約：指定比較射の等式として述べ、可逆な射の存在では代用しない。
使われ方：構造加群の canonical な導来係数拡大比較の可逆性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) [Small.{u} (DiagramModuleCoefficientObject F)]

set_option maxHeartbeats 2000000 in
-- 二つの局所 Yoneda 射と係数遷移による制限を照合するために必要。
/-- 概要：構造加群の指定遷移は局所 regular 比較を通して代表制限比較と一致する。
方針：後合成自然性で生成元の像へ戻し、制限自然性で代表比較を復元する。
規約：KST §3.1。使われ方：導来化と随伴で移す指定経路の可換式。 -/
theorem diagramStructureLocalRegularMap_transition {i j : J} (h : i ≤ j) :
    diagramStructureLocalRegularMap F i ≫
        diagramAlgebraModuleComparison F h (diagramStructureModule F) =
      representableRestrictionMap R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
          (diagramAlgebraVertexTransition F h).op (op .point) ≫
        (moduleRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
          (diagramAlgebraVertexTransition F h).op.op).map
          (diagramStructureLocalRegularMap F j) := by
  change representableUnitMap R (op .point)
      (ForgetEnrichment.to (Complex R)
        ((diagramAlgebraModuleEvaluation F i).obj (diagramStructureModule F)))
      (diagramStructureLocalUnit F i) ≫
        diagramAlgebraModuleComparison F h (diagramStructureModule F) = _
  rw [representableUnitMap_postcomp, diagramStructureLocalUnit_transition]
  exact representableUnitMap_restrict R (diagramAlgebraVertexTransition F h).op (op .point)
    (diagramStructureLocalRaw F j) (diagramStructureLocalUnit F j)

end SerrePositivity.KST.DerivedBlowup
