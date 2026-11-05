module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.KST.Fibration.WeakSpanKanQuotientZeroUnit

/-!
概要：同じ元の固定終点の零単体単位を、元の固定 span の Kan 置換単位へ戻す。
方針：既存指定値比較の終点座標を輸送し、元の置換単位の自然性を使う。
規約：元の全族単位と既存指定値比較だけを使い、存在入力を追加しない。
使われ方：K-B-S の実全族写像の全 fiber 単位回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌)

/-- 概要：元の商 fiber から、元の固定終点の span の同じ Kan 値へ戻す指定比較。
方針：既存指定値比較と元の Kan fiber 比較の両端を、元の終点等式で輸送する。
規約：比較辺を選び直さず、元の同じ Kan 置換を使う。
使われ方：実全族の各元の固定 fiber の単位回収の正規化。 -/
def weakSpanKanQuotientZeroValueComparison :
    vertexFiber (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
      (q.hom.app (Opposite.op ⦋0⦌) y) ⟶
      F2.continuousKanReplacement.obj (fixedMarkedSpans B.obj (weakEquivalences i) x y) :=
  eqToHom (congrArg (vertexFiber
    (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)))
    (congrArg (q.hom.app (Opposite.op ⦋0⦌)) (transportSimplexFirstVertexMap_zeroIndex y)).symm) ≫
    (weakSpanKanQuotientFiberValueEquivalence h x (transportSimplexIndex (n := ⦋0⦌) y)).hom ≫
    weakSpanKanValueComparison i x (transportSimplexIndex (n := ⦋0⦌) y) ≫
    strictKanCompletion.map (eqToHom (congrArg
      (fun z => fixedMarkedSpans B.obj (weakEquivalences i) x z)
      (transportSimplexFirstVertexMap_zeroIndex y)))

/-- 概要：元の終点へ戻した同じ指定値比較は、実 Kan 複体間の同値。
方針：元の fiber 座標同型・既存値同値・元の Kan 値比較の同値性を合成する。
規約：同じ実比較射自体の同値性を示す。
使われ方：元の実 fiber 内の比較を値側から反映する。 -/
theorem weakSpanKanQuotientZeroValueComparison_isQCatEquivalence :
    IsQCatEquivalence (weakSpanKanQuotientZeroValueComparison h x y) := by
  let c := transportSimplexIndex (n := ⦋0⦌) y
  let t := eqToIso (congrArg (vertexFiber
    (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)))
    (congrArg (q.hom.app (Opposite.op ⦋0⦌)) (transportSimplexFirstVertexMap_zeroIndex y)).symm)
  let s := eqToIso (congrArg (fun z => fixedMarkedSpans B.obj (weakEquivalences i) x z)
    (transportSimplexFirstVertexMap_zeroIndex y))
  exact (((qCatEquivalenceOfIso t).isQCatEquivalence.comp
    (weakSpanKanQuotientFiberValueEquivalence h x c).isQCatEquivalence).comp
    (weakSpanKanValueComparison_isQCatEquivalence i x c)).comp
    (strictKanCompletion_map_isQCatEquivalence s.hom (by infer_instance))

/-- 概要：元の終点へ戻した同じ実零単体単位は、元の全 Kan 置換単位を回収する。
方針：元の全 fiber 回収を両端輸送し、元の置換単位の自然性で正規化する。
規約：同じ元の固定 span 全体の関手同型。追加の比較入力は不要。
使われ方：元の実全族の固定 fiber 比較への後合成。 -/
def weakSpanKanQuotientZeroUnit_recovery :
    FunctorIso (weakSpanKanQuotientZeroUnit h x y ≫ weakSpanKanQuotientZeroValueComparison h x y)
      (F2.continuousKanReplacementUnit.app (fixedMarkedSpans B.obj (weakEquivalences i) x y)) := by
  let c := transportSimplexIndex (n := ⦋0⦌) y
  let s := eqToIso (congrArg (fun z => fixedMarkedSpans B.obj (weakEquivalences i) x z)
    (transportSimplexFirstVertexMap_zeroIndex y))
  let t := eqToIso (congrArg (vertexFiber
    (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)))
    (congrArg (q.hom.app (Opposite.op ⦋0⦌)) (transportSimplexFirstVertexMap_zeroIndex y)))
  have e := (FunctorIso.precomp (weakSpanKanQuotientSimplexUnitFiber_recovery h x c) s.inv).postcomp
    (strictKanCompletion.map s.hom)
  have hn := F2.continuousKanReplacementUnit.naturality s.hom
  have hr : s.inv ≫ F2.continuousKanReplacementUnit.app
        (fixedMarkedSpans B.obj (weakEquivalences i) x
          ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))) ≫
      strictKanCompletion.map s.hom =
      F2.continuousKanReplacementUnit.app (fixedMarkedSpans B.obj (weakEquivalences i) x y) := by
    have hh := congrArg (fun f => s.inv ≫ f) hn.symm
    simp only [Functor.id_map, ← Category.assoc, s.inv_hom_id, Category.id_comp] at hh
    simpa only [strictKanCompletion, Category.assoc] using! hh
  have e' := e ≪≫ eqToIso (congrArg HomotopyCategory.mk (congrArg functorVertex hr))
  change FunctorIso
    ((s.inv ≫ weakSpanKanQuotientSimplexUnitFiber h x c ≫ t.hom) ≫
      (t.inv ≫ (weakSpanKanQuotientFiberValueEquivalence h x c).hom ≫
        weakSpanKanValueComparison i x c ≫ strictKanCompletion.map s.hom)) _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [Category.assoc] using! e'

/-- 概要：元の実全族写像の全固定 fiber は、元の Kan 置換単位を回収する。
方針：同じ fiber 内の実全族比較と同じ零単体の厳密照合を元の全単位回収へ合成する。
規約：元の全族・q・各終点・全固定 span を保持し、点別の比較へ弱めない。
使われ方：K-B-S の全 fiber 単位条件。指定恒等点との比較は別に確認する。 -/
def weakSpanKanQuotientFamilyFixedFiber_recovery :
    FunctorIso
      (weakSpanKanQuotientFamilyFixedFiber h x y ≫ weakSpanKanQuotientZeroValueComparison h x y)
      (F2.continuousKanReplacementUnit.app (fixedMarkedSpans B.obj (weakEquivalences i) x y)) := by
  have e := (weakSpanKanQuotientFamilyFixedFiberIso h x y).postcomp
    (weakSpanKanQuotientZeroValueComparison h x y)
  rw [← weakSpanKanQuotientZeroUnit_eq_fixedFiber h x y] at e
  exact e ≪≫ weakSpanKanQuotientZeroUnit_recovery h x y

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber_recovery (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiber_recovery := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber_recovery

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroUnit_recovery (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroUnit_recovery := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroUnit_recovery

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroValueComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroValueComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroValueComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroValueComparison_isQCatEquivalence := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroValueComparison_isQCatEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiber_recovery._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber_recovery._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroUnit_recovery._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroUnit_recovery._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroUnit_recovery._proof_10 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroUnit_recovery._proof_10

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroUnit_recovery._proof_11 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroUnit_recovery._proof_11

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroUnit_recovery._proof_12 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroUnit_recovery._proof_12

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroUnit_recovery._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroUnit_recovery._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroUnit_recovery._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroUnit_recovery._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroUnit_recovery._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroUnit_recovery._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroUnit_recovery._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroUnit_recovery._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroUnit_recovery._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroUnit_recovery._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroUnit_recovery._proof_7 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroUnit_recovery._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroUnit_recovery._proof_8 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroUnit_recovery._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroUnit_recovery._proof_9 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroUnit_recovery._proof_9

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroUnit_recovery._simp_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroUnit_recovery._simp_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroValueComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroValueComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroValueComparison._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroValueComparison._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroValueComparison._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroValueComparison._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroValueComparison._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroValueComparison._proof_4
