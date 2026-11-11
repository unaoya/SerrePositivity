module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 概要：同じ零単体値比較は既存指定恒等点を、元の Kan 恒等点へ送る。
方針：同じ全 fiber の値比較同型を既存指定点で評価する。
規約：元の指定点を変更しない。
使われ方：元の全族の Kan 単位回収と既存指定点の正規化の接続。 -/
def weakIdentityQuotientZeroValue_pointIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((weakIdentityQuotientZeroValueComparison h x).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberPoint h x)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app (weakIdentityQuotientZeroValueIso h x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberPoint h x) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberValue_pointIso h x

/-- 概要：元の全族の同じ指定値比較で、既存指定恒等点は元の恒等 span の Kan 単位像へ戻る。
方針：元の Kan 値比較の恒等点公式と同じ終点輸送の置換単位自然性を使う。
規約：元の固定 span と同じ Kan 置換単位を保持する。
使われ方：同じ実商 fiber 内の指定点比較を値側から反映する。 -/
def weakIdentityQuotientZeroComparison_pointIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientZeroValueComparison h x x).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberPoint h x))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app
        (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x x)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpan h x)) := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x
  let s := eqToIso (congrArg (fun y => fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex x))
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroValue_pointIso h x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanValueComparison i x c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.strictKanCompletion.map s.hom)
  have hn := congrArg (fun f => f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex h x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality s.hom)
  have hi : s.hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex h x) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpan h x := by
    exact congrArg (fun f => f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpan h x)) s.inv_hom_id
  have hr : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanValueComparison i x c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.strictKanCompletion.map s.hom).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpan h x) := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.strictKanCompletion.map s.hom).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanValueComparison i x c).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint_valueComparison]
    exact hn.symm.trans (congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app _).app
      (Opposite.op ⦋0⦌)) hi)
  have e' := e ≪≫ eqToIso (congrArg HomotopyCategory.mk hr)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientZeroValueComparison, weakIdentityQuotientZeroValueComparison,
    s, Category.assoc] using! e'

/-- 概要：元の実全族写像の恒等 span 像は、既存指定恒等点と同じ商 fiber 内で同型。
方針：同じ元の全 fiber 単位回収と既存指定点の正規化を、同じ値比較の充満忠実性で反映する。
規約：元の全族写像・q・weakIdentityQuotientFiberPoint を保持する。
使われ方：K-B-S の Sp-6 s4 へ供給する指定恒等点条件。 -/
def weakSpanKanQuotientFamilyFixedFiber_identityIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber h x x).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpan h x)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberPoint h x) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber_recovery h x x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpan h x)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientZeroValueComparison_isQCatEquivalence h x x).isFullyFaithful.preimageVertexIso
    (e ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroComparison_pointIso h x).symm)

/-- 概要：元の全族の全固定 fiber 制限を含めると、同じ元の全族写像を厳密回収する。
方針：同じ元の fiber 持ち上げの包含後の式を使う。
規約：全固定 span 上の実写像の等式。
使われ方：全 fiber 単位・指定恒等点条件が同じ実全族写像に対する条件であることの確認。 -/
theorem weakSpanKanQuotientFamilyFixedFiber_ι (y : B.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber h x y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
        (q.hom.app (Opposite.op ⦋0⦌) y) =
      fixedMarkedSpanToFamily B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y ≫ weakSpanKanQuotientFamilyMap h x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroComparison_pointIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityQuotientZeroComparison_pointIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroComparison_pointIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroValue_pointIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityQuotientZeroValue_pointIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroValue_pointIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber_identityIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiber_identityIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber_identityIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiber_ι := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityQuotientZeroComparison_pointIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroComparison_pointIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityQuotientZeroComparison_pointIso._proof_10 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroComparison_pointIso._proof_10

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityQuotientZeroComparison_pointIso._proof_11 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroComparison_pointIso._proof_11

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityQuotientZeroComparison_pointIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroComparison_pointIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityQuotientZeroComparison_pointIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroComparison_pointIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityQuotientZeroComparison_pointIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroComparison_pointIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityQuotientZeroComparison_pointIso._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroComparison_pointIso._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityQuotientZeroComparison_pointIso._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroComparison_pointIso._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityQuotientZeroComparison_pointIso._proof_7 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroComparison_pointIso._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityQuotientZeroComparison_pointIso._proof_8 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroComparison_pointIso._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityQuotientZeroComparison_pointIso._proof_9 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroComparison_pointIso._proof_9

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityQuotientZeroValue_pointIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroValue_pointIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityQuotientZeroValue_pointIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientZeroValue_pointIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiber_identityIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber_identityIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiber_identityIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber_identityIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiber_identityIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber_identityIso._proof_3
