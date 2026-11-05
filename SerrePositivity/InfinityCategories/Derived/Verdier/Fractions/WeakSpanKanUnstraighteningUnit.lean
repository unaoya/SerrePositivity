module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanFiberUnit
public import SerrePositivity.InfinityCategories.F1.Diagrams.CocartesianKanUnstraighteningUnitPoints

/-!
概要：元の span 射影の単体圏引き戻しから、同じ Kan 図式への実全族単位を供給する。
方針：Ind-S (5) の公開構成を元の射影・Kan 置換・単位へそのまま代入する。
規約：単位と厳密な底条件と全 fiber 回収を同じ存在証拠から選ぶ。商への降下は別工程。
使われ方：K-B-S の相対初頂点降下と元の全 fiber 単位の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {A B : StableCategory.{u}} (i : ExactMap A B) (x : B.obj _⦋0⦌)

/-- 概要：同じ元の span 全族の引き戻しから、同じ Kan unstraightening への実単位。
方針：Ind-S (5) の元の cocartesian 射影への存在定理から選ぶ。
規約：η の anodyne 性を追加仮定にせず、元の全空間を保持する。
使われ方：K-B-S の単体圏上の全族単位。 -/
def weakSpanKanUnstraighteningUnit :
    pullback (markedSpanFamilyProjection B.obj (weakEquivalences i) x)
      (transportSimplexFirstVertexMap B.obj) ⟶
        smallLeftUnstraightening (weakSpanKanCoherentDiagram i x) :=
  (exists_cocartesianKanUnstraighteningUnit (weakSpanSimplexProjection i x)
    strictKanCompletion F2.continuousKanReplacementUnit).choose

/-- 概要：同じ実単位は元の単体圏射影を厳密に保持する。
方針：全 fiber 回収も保持する同じ存在証拠から底条件を取り出す。
規約：全族写像を別に選び直さない。
使われ方：同じ商上の全族射へ後合成する底条件。 -/
theorem weakSpanKanUnstraighteningUnit_projection :
    weakSpanKanUnstraighteningUnit i x ≫
      smallLeftUnstraighteningProjection (weakSpanKanCoherentDiagram i x) =
        weakSpanSimplexProjection i x :=
  (exists_cocartesianKanUnstraighteningUnit (weakSpanSimplexProjection i x)
    strictKanCompletion F2.continuousKanReplacementUnit).choose_spec.choose

/-- 概要：同じ実単位の全 fiber 写像は元の Kan 置換単位を回収する。
方針：Ind-S (5) が実全族と同時に供給した全関手同型を読む。
規約：対象別の単位や同値を独立に選ばない。
使われ方：元の固定 span fiber への単位回収の入力。 -/
def weakSpanKanUnstraighteningUnit_fiberRecovery (c : TransportSimplexCategory B.obj) :
    FunctorIso
      (vertexFiberMap (weakSpanSimplexProjection i x)
        (smallLeftUnstraighteningProjection (weakSpanKanCoherentDiagram i x))
        (weakSpanKanUnstraighteningUnit i x)
        (weakSpanKanUnstraighteningUnit_projection i x) (nerveVertex c) ≫
      (smallLeftUnstraighteningFiberValueEquivalence (weakSpanKanCoherentDiagram i x)
        (nerveVertex c)).hom ≫
      strictKanCompletion.map (cocartesianStrictTransportEvaluate (weakSpanSimplexProjection i x) c))
      (F2.continuousKanReplacementUnit.app
        (vertexFiber (weakSpanSimplexProjection i x) (nerveVertex c))) :=
  Classical.choice ((exists_cocartesianKanUnstraighteningUnit (weakSpanSimplexProjection i x)
    strictKanCompletion F2.continuousKanReplacementUnit).choose_spec.choose_spec c)

/-- 概要：元の両端固定 span 全体の同じ単位は、元の Kan 置換単位を全体として回収する。
方針：同じ実 fiber 回収を元の fiber 同型で前合成し、元の逆同型の Kan 像で後合成する。
規約：各 fiber の全関手同型を保持し、恒等点だけの照合へ弱めない。
使われ方：K-B-S の全 fiber 条件を元の固定 span 座標へ戻す。 -/
def weakSpanKanUnstraighteningUnit_fixedFiberRecovery (c : TransportSimplexCategory B.obj) :
    FunctorIso
      ((weakSpanSimplexFiberIso i x c).hom ≫
        vertexFiberMap (weakSpanSimplexProjection i x)
          (smallLeftUnstraighteningProjection (weakSpanKanCoherentDiagram i x))
          (weakSpanKanUnstraighteningUnit i x)
          (weakSpanKanUnstraighteningUnit_projection i x) (nerveVertex c) ≫
        (smallLeftUnstraighteningFiberValueEquivalence (weakSpanKanCoherentDiagram i x)
          (nerveVertex c)).hom ≫ weakSpanKanValueComparison i x c)
      (F2.continuousKanReplacementUnit.app _) := by
  let s := weakSpanSimplexFiberIso i x c
  have e := ((weakSpanKanUnstraighteningUnit_fiberRecovery i x c).precomp s.hom).postcomp
    (strictKanCompletion.map s.inv)
  have hn := F2.continuousKanReplacementUnit.naturality s.inv
  have hr : s.hom ≫ F2.continuousKanReplacementUnit.app
      (vertexFiber (weakSpanSimplexProjection i x) (nerveVertex c)) ≫
      strictKanCompletion.map s.inv =
      F2.continuousKanReplacementUnit.app
        (fixedMarkedSpans B.obj (weakEquivalences i) x
          ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))) := by
    have hh := congrArg (fun f => s.hom ≫ f) hn.symm
    simp only [Functor.id_map, ← Category.assoc, s.hom_inv_id, Category.id_comp] at hh
    simpa only [_root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion, Category.assoc] using! hh
  have e' := e ≪≫ eqToIso (congrArg HomotopyCategory.mk (congrArg functorVertex hr))
  simpa only [weakSpanKanValueComparison, cocartesianKanDiagramFiberComparison,
    s, Category.assoc] using! e'


/-- 概要：同じ実単位の元の固定 span fiber 上の値は、既存の全 fiber 単位と関手同型。
方針：元の値比較による全単位回収を、その後合成の充満忠実性で反映する。
規約：対象別の同型の選択へ弱めず、同じ全関手空間内の同型を得る。
使われ方：商比較の指定 transport と既存の恒等 span 値への接続。 -/
def weakSpanKanUnstraighteningUnit_fixedFiberIso (c : TransportSimplexCategory B.obj) :
    FunctorIso
      ((weakSpanSimplexFiberIso i x c).hom ≫
        vertexFiberMap (weakSpanSimplexProjection i x)
          (smallLeftUnstraighteningProjection (weakSpanKanCoherentDiagram i x))
          (weakSpanKanUnstraighteningUnit i x)
          (weakSpanKanUnstraighteningUnit_projection i x) (nerveVertex c) ≫
        (smallLeftUnstraighteningFiberValueEquivalence (weakSpanKanCoherentDiagram i x)
          (nerveVertex c)).hom)
      (weakSpanKanFiberUnit i x c) := by
  have e := weakSpanKanUnstraighteningUnit_fixedFiberRecovery i x c
  rw [← weakSpanKanFiberUnit_valueComparison i x c] at e
  apply ((weakSpanKanValueComparison_isQCatEquivalence i x c).postcompose
    (fixedMarkedSpans B.obj (weakEquivalences i) x
      ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
        (nerveVertex c)))).isFullyFaithful.preimageVertexIso
  simpa only [Category.assoc] using! e

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fiberRecovery (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fiberRecovery := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fiberRecovery

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberRecovery (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberRecovery := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberRecovery

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_projection := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_projection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fiberRecovery._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fiberRecovery._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fiberRecovery._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fiberRecovery._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fiberRecovery._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fiberRecovery._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fiberRecovery._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fiberRecovery._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_10 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_10

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_7 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_8 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_9 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._proof_9

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._simp_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_fixedFiberRecovery._simp_1
