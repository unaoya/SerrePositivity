module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakIdentityKanValue

/-!
概要：元の固定分数 span の全 fiber を同じ strict Kan 図式の値へ写す単位。
方針：恒等射評価の自明 Kan fibration の切断と元の Kan 置換単位を合成する。
規約：各 fiber の全単体の等式を保持し、可変終点の全族写像は主張しない。
使われ方：商上の小さい unstraightening への全族単位を照合するための指定制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {A B : StableCategory.{u}} (i : ExactMap A B) (x : B.obj _⦋0⦌)

/-- 概要：同じ全 section の恒等射評価を、fiber の全単体上で厳密に切断する。
方針：自明 Kan fibration の切断を選ぶ。
規約：選択は fiber 全体に一度だけ行う。
使われ方：元の Kan 単位を図式値へ持ち上げる。 -/
def weakSpanStrictEvaluationSection (c : TransportSimplexCategory B.obj) :
    vertexFiber (weakSpanSimplexProjection i x) (nerveVertex c) ⟶
      SerrePositivity.InfinityCategories.cocartesianStrictTransport
        (weakSpanSimplexProjection i x) c :=
  Classical.choose (trivialKanFibration_exists_section
    (SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate
      (weakSpanSimplexProjection i x) c))

/-- 概要：元の両端固定 span の全体を、同じ Kan 図式の値へ送る。
方針：元の fiber 同型、評価の切断、元の置換単位を順に使う。
規約：可変終点に関する自然性はまだ主張しない。
使われ方：全族単位に要求する各 fiber の指定写像。 -/
def weakSpanKanFiberUnit (c : TransportSimplexCategory B.obj) :
    fixedMarkedSpans B.obj (weakEquivalences i) x
      ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)) ⟶
      ((weakSpanKanDiagram i x).obj c).obj :=
  (weakSpanSimplexFiberIso i x c).hom ≫ weakSpanStrictEvaluationSection i x c ≫
    F2.continuousKanReplacementUnit.app _

/-- 概要：同じ値の比較後に、元の Kan 置換単位を fiber 全体で厳密に回収する。
方針：置換の自然性と評価の切断等式を使う。
規約：頂点だけでなく単体集合の射の等式。
使われ方：K-B-S の全 fiber 回収条件の右辺。 -/
theorem weakSpanKanFiberUnit_valueComparison (c : TransportSimplexCategory B.obj) :
    weakSpanKanFiberUnit i x c ≫ weakSpanKanValueComparison i x c =
      F2.continuousKanReplacementUnit.app _ := by
  let s := weakSpanSimplexFiberIso i x c
  let e := SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate
    (weakSpanSimplexProjection i x) c
  have hs : weakSpanStrictEvaluationSection i x c ≫ e = 𝟙 _ :=
    Classical.choose_spec (trivialKanFibration_exists_section e)
  change s.hom ≫ (weakSpanStrictEvaluationSection i x c ≫
      F2.continuousKanReplacementUnit.app _) ≫
      (F2.continuousKanReplacement.map e ≫ F2.continuousKanReplacement.map s.inv) = _
  calc
    _ = (s.hom ≫ (weakSpanStrictEvaluationSection i x c ≫ e) ≫ s.inv) ≫
        F2.continuousKanReplacementUnit.app _ := by
      have hn := (F2.continuousKanReplacementUnit.naturality (e ≫ s.inv)).symm
      simpa only [Functor.map_comp, Functor.id_map, Category.assoc] using!
        congrArg (fun m => s.hom ≫ weakSpanStrictEvaluationSection i x c ≫ m) hn
    _ = _ := by rw [hs, Category.id_comp, s.hom_inv_id, Category.id_comp]


/-- 概要：恒等 span の像は、既存の同じ指定 Kan 恒等点そのもの。
方針：零単体添字で切断と元の fiber 同型の定義を照合する。
規約：恒等点を新たに選ばない。
使われ方：K-B-S の指定恒等点への fiber 内比較。 -/
theorem weakSpanKanFiberUnit_identity {C : StableCategory.{u}} {q : ExactMap B C}
    (h : IsVerdierSequence i q) :
    (weakSpanKanFiberUnit i x (transportSimplexIndex (n := ⦋0⦌) x)).app
      (Opposite.op ⦋0⦌) (weakIdentityFixedSpanAtZeroIndex h x) =
        weakIdentityKanPoint h x := rfl

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanFiberUnit (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanFiberUnit := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanFiberUnit

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanFiberUnit_identity := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanFiberUnit_identity

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanFiberUnit_valueComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanFiberUnit_valueComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanStrictEvaluationSection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanStrictEvaluationSection := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanStrictEvaluationSection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanFiberUnit._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanFiberUnit._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanFiberUnit._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanFiberUnit._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanFiberUnit._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanFiberUnit._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanFiberUnit._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanFiberUnit._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanFiberUnit._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanFiberUnit._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanStrictEvaluationSection._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanStrictEvaluationSection._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanStrictEvaluationSection._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanStrictEvaluationSection._proof_2
