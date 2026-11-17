module

public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitCarrierDerivedComparison

/-!
# 一般導来極限の底の比較の自然性と右導来関手への比較

概要：BM 命題 4.1・Hovey §5.4 の底の一般導来極限比較を自然同型へ束ねる。
方針：両 Hom 同値の終域自然性と元の右導来極限の一意性を使う。
規約：元の E 代数図式と元の底の計算対象を保持する。
使われ方：E2a-4 の一般 homotopy 極限の忘却後の導来比較。
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 2048
-- 二つの具体的な Hom 同値と普通の局所化の型を同時に照合するため。

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra Opposite
open SerrePositivity.DifferentialGraded

attribute [local irreducible] rightFrameFamily ComplexLimits.rightFrameFamily
  carrierFramedLimitComparisonIso carrierFramedLimitDerivedHomEquiv
  ComplexLimits.framedLimitDerivedHomEquiv framedLimitFunctor ComplexLimits.framedLimitFunctor

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：底の導来極限の同じ比較同型は元の図式射に自然（Hovey §5.4）。
方針：始域に複体の計算対象を取り、その恒等射の Hom 表示を両終域へ送る。
規約：別の比較同型を選ばない。
使われ方：底の導来極限比較を自然同型に束ねる。 -/
lemma carrierFramedLimitComparisonIso_naturality {F G : K ⥤ (operad A).Algebra}
    (g : F ⟶ G) :
    let := projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    Q.map ((ComplexLimits.framedLimitFunctor A K).map ((Diagram.forget A K).map g)) ≫
        (carrierFramedLimitComparisonIso A K G).hom =
      (carrierFramedLimitComparisonIso A K F).hom ≫
        Q.map ((framedLimitFunctor A K).map g).hom := by
  let := projectiveModelCategory A
  let := CarrierDiagram.projectiveModelCategory A K
  let Q := (weakEquivalences (Complex A)).Q
  let QD := (weakEquivalences (K ⥤ Complex A)).Q
  let Fc := (Diagram.forget A K).obj F
  let Gc := (Diagram.forget A K).obj G
  let gc := (Diagram.forget A K).map g
  let Y := (ComplexLimits.framedLimitFunctor A K).obj Fc
  let eF := ComplexLimits.framedLimitDerivedHomEquiv A K Y Fc
  let eG := ComplexLimits.framedLimitDerivedHomEquiv A K Y Gc
  let z := eF.symm (𝟙 (Q.obj Y))
  have hz : eF z = 𝟙 (Q.obj Y) := eF.apply_symm_apply _
  have hc : eG (z ≫ QD.map gc) = Q.map ((ComplexLimits.framedLimitFunctor A K).map gc) :=
    (ComplexLimits.framedLimitDerivedHomEquiv_target A K Y gc z).trans
      ((congrArg (fun t => t ≫ Q.map ((ComplexLimits.framedLimitFunctor A K).map gc)) hz).trans
        (Category.id_comp _))
  have he : eG.symm (Q.map ((ComplexLimits.framedLimitFunctor A K).map gc)) =
      z ≫ QD.map gc := by
    simpa only [Equiv.symm_apply_apply] using (congrArg eG.symm hc).symm
  have hF : (carrierFramedLimitComparisonIso A K F).hom =
      carrierFramedLimitDerivedHomEquiv A K Y F z :=
    (Category.id_comp _).symm.trans (carrierFramedLimitComparisonIso_hom_apply A K F Y (𝟙 _))
  exact (carrierFramedLimitComparisonIso_hom_apply A K G Y _).trans
    (((congrArg (carrierFramedLimitDerivedHomEquiv A K Y G) he).trans
      (carrierFramedLimitDerivedHomEquiv_target A K Y g z)).trans
        (congrArg (fun t => t ≫ Q.map ((framedLimitFunctor A K).map g).hom) hF.symm))

/-- 概要：一般導来極限の底の比較を同じ成分の自然同型へ束ねる（BM 命題 4.1）。
方針：構成済みの比較同型と元の図式射の自然性を使う。
規約：複体図式全体の計算関手を忘却図式へ制限する。
使われ方：E 代数の一般 homotopy 極限の底の計算。 -/
def carrierFramedLimitComparisonNatIso :
    let := projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    Diagram.forget A K ⋙ ComplexLimits.framedLimitFunctor A K ⋙ Q ≅
      framedLimitFunctor A K ⋙ Operad.Algebra.forget (operad A) ⋙ Q := by
  let := projectiveModelCategory A
  let Q := (weakEquivalences (Complex A)).Q
  dsimp only
  refine NatIso.ofComponents (fun F => ?_) ?_
  · change Q.obj ((ComplexLimits.framedLimitFunctor A K).obj
      ((Diagram.forget A K).obj F)) ≅ Q.obj ((framedLimitFunctor A K).obj F).carrier
    exact carrierFramedLimitComparisonIso A K F
  · intro F G g
    change Q.map ((ComplexLimits.framedLimitFunctor A K).map ((Diagram.forget A K).map g)) ≫
        (carrierFramedLimitComparisonIso A K G).hom =
      (carrierFramedLimitComparisonIso A K F).hom ≫
        Q.map ((framedLimitFunctor A K).map g).hom
    exact carrierFramedLimitComparisonIso_naturality A K g

/-- 概要：元の E 代数極限の底は任意の底の右導来極限の値と同型（BM 命題 4.1）。
方針：同じ具体的な複体計算との比較と右導来関手の一意性を合成する。
規約：忘却した元の図式の普通の局所化像で評価する。
使われ方：E2a-4 の一般右導来極限比較の界面。 -/
def framedLimitCarrierDerivedIso (F : K ⥤ (operad A).Algebra) :
    let := projectiveModelCategory A
    let := CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    let QD := (weakEquivalences (K ⥤ Complex A)).Q
    ∀ (RF : (weakEquivalences (K ⥤ Complex A)).Localization ⥤
        (weakEquivalences (Complex A)).Localization)
      (β : lim ⋙ Q ⟶ QD ⋙ RF),
      RF.IsRightDerivedFunctor β (weakEquivalences (K ⥤ Complex A)) →
      (Q.obj ((framedLimitFunctor A K).obj F).carrier ≅
        RF.obj (QD.obj ((Diagram.forget A K).obj F))) := by
  let := projectiveModelCategory A
  let := CarrierDiagram.projectiveModelCategory A K
  dsimp only
  intro RF β hRF
  exact (carrierFramedLimitComparisonIso A K F).symm ≪≫
    ComplexLimits.framedLimitDerivedIso A K ((Diagram.forget A K).obj F) RF β hRF

end SerrePositivity.EInfinity.BarrattEccles
