module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeGraphIso
public import SerrePositivity.DifferentialGraded.Morita.KernelNaturality

/-!
概要：KST §3.1 の包含 gauge の通常係数拡大上の指定自己同型。
方針：graph bimodule 同型の通常 tensor 作用を使い、純斉次 tensor 上の公式を示す。
規約：始点の加群を変えず、graph の因子を重み付けする。
使われ方：捻りの指定加群比較と延長–制限随伴の計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)

/-- 概要：通常の局所係数拡大に対する指定 gauge 自然自己同型。
方針：graph 同型の順逆を通常 kernel の tensor 作用へ送り、合成保存を使う。
規約：KST §3.1。使われ方：通常随伴の可逆な重み付け。 -/
def diagramGaugeModuleExtensionIso {i j : J} (h : i ≤ j) :
    (dgModuleExtension R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
        (diagramAlgebraVertexTransition F h).op).onClosed ≅
      (dgModuleExtension R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
        (diagramAlgebraVertexTransition F h).op).onClosed where
  hom := Morita.kernelTensorMap R _ _ (diagramGaugeGraphIso F s h).hom
  inv := Morita.kernelTensorMap R _ _ (diagramGaugeGraphIso F s h).inv
  hom_inv_id := by
    rw [← Morita.kernelTensorMap_comp, Iso.hom_inv_id, Morita.kernelTensorMap_id]
    rfl
  inv_hom_id := by
    rw [← Morita.kernelTensorMap_comp, Iso.inv_hom_id, Morita.kernelTensorMap_id]
    rfl

set_option maxHeartbeats 2000000 in
-- graph の右加群評価と左加群評価の balanced tensor の型を照合するために必要。
/-- 概要：指定通常係数拡大自己同型は純 tensor の graph 因子に gauge を作用させる。
方針：通常 kernel 作用の値の公式と balanced tensor map の生成元公式を使う。
規約：KST §3.1。使われ方：単位挿入と余単位による随伴像の計算。 -/
theorem diagramGaugeModuleExtensionIso_element {i j : J} (h : i ≤ j)
    (M : ModuleCategory R (AlgebraVertex (F.obj i))ᵒᵖ) {r q n : ℤ}
    (m : ((ForgetEnrichment.to (Complex R) M).obj (op (op .point))).X r)
    (z : (F.obj j).X.X q) (hn : r + q = n) :
    (((moduleEvaluation R (AlgebraVertex (F.obj j))ᵒᵖ (op .point)).map
        ((diagramGaugeModuleExtensionIso F s h).hom.app M)).f n)
      (BalancedTensor.element R (AlgebraVertex (F.obj i))ᵒᵖ
        (ForgetEnrichment.to (Complex R) M)
        ((functorGraph R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
          (diagramAlgebraVertexTransition F h).op).leftAt (op .point)) (op .point) m z hn) =
      BalancedTensor.element R (AlgebraVertex (F.obj i))ᵒᵖ
        (ForgetEnrichment.to (Complex R) M)
        ((functorGraph R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
          (diagramAlgebraVertexTransition F h).op).leftAt (op .point)) (op .point) m
        (((s.scale h).hom.f q) z) hn := by
  change (((moduleEvaluation R (AlgebraVertex (F.obj j))ᵒᵖ (op .point)).map
    ((Morita.kernelTensorMap R _ _ (diagramGaugeGraphIso F s h).hom).app M)).f n) _ = _
  rw [Morita.kernelTensorMap_value]
  have he := BalancedTensor.map_element R (AlgebraVertex (F.obj i))ᵒᵖ (𝟙 M)
    ((BimoduleCategory.leftEvaluation R (AlgebraVertex (F.obj j))ᵒᵖ
      (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map (diagramGaugeGraphIso F s h).hom)
    (op .point) m z hn
  refine he.trans ?_
  rw [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.id_apply,
    BimoduleCategory.leftEvaluation_map_eval]
  change BalancedTensor.element R (AlgebraVertex (F.obj i))ᵒᵖ
      (ForgetEnrichment.to (Complex R) M)
      ((functorGraph R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
        (diagramAlgebraVertexTransition F h).op).leftAt (op .point)) (op .point) m
      ((((moduleEvaluation R (AlgebraVertex (F.obj j))ᵒᵖ (op .point)).map
        ((BimoduleCategory.evaluation R (AlgebraVertex (F.obj j))ᵒᵖ
          (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
          (diagramGaugeGraphIso F s h).hom)).f q) z) hn = _
  rw [diagramGaugeGraphIso_hom_eval, diagramGaugeRegularIso_hom_eval]
  rfl

end SerrePositivity.KST.DerivedBlowup
