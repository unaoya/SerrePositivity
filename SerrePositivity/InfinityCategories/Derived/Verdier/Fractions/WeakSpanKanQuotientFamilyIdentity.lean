module
public import SerrePositivity.KST.Fibration.WeakIdentityQuotientZeroValue

/-!
概要：元の実全族写像の恒等 span 像を、既存指定恒等点へ同じ実 fiber 内で比較する。
方針：元の全 fiber 単位回収と既存指定点の同じ値正規化を、指定値比較の充満忠実性で反映する。
規約：元の weakIdentityQuotientFiberPoint を保持し、補助点へ置換しない。
使われ方：K-B-S の Sp-6 s4 向け実全族単位の指定恒等点条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 概要：同じ零単体値比較は既存指定恒等点を、元の Kan 恒等点へ送る。
方針：同じ全 fiber の値比較同型を既存指定点で評価する。
規約：元の指定点を変更しない。
使われ方：元の全族の Kan 単位回収と既存指定点の正規化の接続。 -/
def weakIdentityQuotientZeroValue_pointIso :
    VertexIso ((weakIdentityQuotientZeroValueComparison h x).app (Opposite.op ⦋0⦌)
      (weakIdentityQuotientFiberPoint h x)) (weakIdentityKanPoint h x) :=
  FunctorIso.app (weakIdentityQuotientZeroValueIso h x) (weakIdentityQuotientFiberPoint h x) ≪≫
    weakIdentityQuotientFiberValue_pointIso h x

/-- 概要：元の全族の同じ指定値比較で、既存指定恒等点は元の恒等 span の Kan 単位像へ戻る。
方針：元の Kan 値比較の恒等点公式と同じ終点輸送の置換単位自然性を使う。
規約：元の固定 span と同じ Kan 置換単位を保持する。
使われ方：同じ実商 fiber 内の指定点比較を値側から反映する。 -/
def weakIdentityQuotientZeroComparison_pointIso :
    VertexIso ((weakSpanKanQuotientZeroValueComparison h x x).app (Opposite.op ⦋0⦌)
      (weakIdentityQuotientFiberPoint h x))
      ((F2.continuousKanReplacementUnit.app
        (fixedMarkedSpans B.obj (weakEquivalences i) x x)).app (Opposite.op ⦋0⦌)
          (weakIdentityFixedSpan h x)) := by
  let c := transportSimplexIndex (n := ⦋0⦌) x
  let s := eqToIso (congrArg (fun y => fixedMarkedSpans B.obj (weakEquivalences i) x y)
    (transportSimplexFirstVertexMap_zeroIndex x))
  have e := VertexIso.map (weakIdentityQuotientZeroValue_pointIso h x)
    (weakSpanKanValueComparison i x c ≫ strictKanCompletion.map s.hom)
  have hn := congrArg (fun f => f.app (Opposite.op ⦋0⦌) (weakIdentityFixedSpanAtZeroIndex h x))
    (F2.continuousKanReplacementUnit.naturality s.hom)
  have hi : s.hom.app (Opposite.op ⦋0⦌) (weakIdentityFixedSpanAtZeroIndex h x) =
      weakIdentityFixedSpan h x := by
    exact congrArg (fun f => f.app (Opposite.op ⦋0⦌) (weakIdentityFixedSpan h x)) s.inv_hom_id
  have hr : (weakSpanKanValueComparison i x c ≫ strictKanCompletion.map s.hom).app
      (Opposite.op ⦋0⦌) (weakIdentityKanPoint h x) =
      (F2.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)
        (weakIdentityFixedSpan h x) := by
    change (strictKanCompletion.map s.hom).app (Opposite.op ⦋0⦌)
      ((weakSpanKanValueComparison i x c).app (Opposite.op ⦋0⦌) (weakIdentityKanPoint h x)) = _
    rw [weakIdentityKanPoint_valueComparison]
    exact hn.symm.trans (congrArg ((F2.continuousKanReplacementUnit.app _).app
      (Opposite.op ⦋0⦌)) hi)
  have e' := e ≪≫ eqToIso (congrArg HomotopyCategory.mk hr)
  simpa only [weakSpanKanQuotientZeroValueComparison, weakIdentityQuotientZeroValueComparison,
    s, Category.assoc] using! e'

/-- 概要：元の実全族写像の恒等 span 像は、既存指定恒等点と同じ商 fiber 内で同型。
方針：同じ元の全 fiber 単位回収と既存指定点の正規化を、同じ値比較の充満忠実性で反映する。
規約：元の全族写像・q・weakIdentityQuotientFiberPoint を保持する。
使われ方：K-B-S の Sp-6 s4 へ供給する指定恒等点条件。 -/
def weakSpanKanQuotientFamilyFixedFiber_identityIso :
    VertexIso ((weakSpanKanQuotientFamilyFixedFiber h x x).app (Opposite.op ⦋0⦌)
      (weakIdentityFixedSpan h x)) (weakIdentityQuotientFiberPoint h x) := by
  have e := FunctorIso.app (weakSpanKanQuotientFamilyFixedFiber_recovery h x x)
    (weakIdentityFixedSpan h x)
  exact (weakSpanKanQuotientZeroValueComparison_isQCatEquivalence h x x).isFullyFaithful.preimageVertexIso
    (e ≪≫ (weakIdentityQuotientZeroComparison_pointIso h x).symm)

/-- 概要：元の全族の全固定 fiber 制限を含めると、同じ元の全族写像を厳密回収する。
方針：同じ元の fiber 持ち上げの包含後の式を使う。
規約：全固定 span 上の実写像の等式。
使われ方：全 fiber 単位・指定恒等点条件が同じ実全族写像に対する条件であることの確認。 -/
theorem weakSpanKanQuotientFamilyFixedFiber_ι (y : B.obj _⦋0⦌) :
    weakSpanKanQuotientFamilyFixedFiber h x y ≫
      vertexFiberι (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
        (q.hom.app (Opposite.op ⦋0⦌) y) =
      fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y ≫ weakSpanKanQuotientFamilyMap h x :=
  vertexFiberLift_ι _ _ _ _

end SerrePositivity.KST.Fibration
