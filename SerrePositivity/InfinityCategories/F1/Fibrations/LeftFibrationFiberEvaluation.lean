module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationMappingSpaces
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorFiberHom
public import SerrePositivity.InfinityCategories.F1.Coherent.HomEnrichedNaturality
public import SerrePositivity.InfinityCategories.Core.LeftFiberKan

/-!
概要：固定した底の頂点での fiber の評価を、豊穣関手と 𝒮 値の coherent な関手にする。
方針：相対関手空間の fiber への作用を Hom の作用とし、評価の恒等・合成を各次数で計算する。
規約：底の quasicategory 性は要求しない。
使われ方：Kerodon Corollary 5.6.0.6、straightening の値での写像空間比較の全次数の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：left fibration の指定頂点上の fiber を束縛した Kan 複体として評価する。
方針：left fibration の fiber の Kan 性を添える。
規約：fiber の宇宙は元の全空間と同じ u。
使われ方：Kerodon Corollary 5.6.0.6、fiber の評価の豊穣関手の対象への作用。 -/
def leftFibrationFiberObject {B : SSet.{u}} (b : B _⦋0⦌) (p : LeftFibrationObject B) :
    KanObject.{u} := ⟨vertexFiber p.val.hom b, inferInstance⟩

/-- 概要：指定した頂点で fiber を取る操作は left fibrations の単体的圏から Kan 複体の単体的圏への豊穣関手。
方針：相対 Hom の fiber への制限を用い、恒等と合成をパラメーター付き評価で比較する。
規約：通常の底上の射だけでなく、相対 Hom の全高次単体を写す。
使われ方：Kerodon Corollary 5.6.0.6、分類の fibration 側の値の評価。 -/
noncomputable def leftFibrationFiberEvaluationEnriched {B : SSet.{u}} (b : B _⦋0⦌) :
    EnrichedFunctor SSet.{u} (LeftFibrationObject B) KanObject.{u} where
  obj := leftFibrationFiberObject b
  map p q := relativeFunctorFiberHom p.val.hom q.val.hom b
  map_id p := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl
  map_comp p q r := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl

/-- 概要：left fibrations の ∞ 圏から 𝒮 への、指定頂点における fiber の評価関手。
方針：fiber の豊穣評価に coherent nerve の後合成を適用する。
規約：始域と標的はともに u+1 の quasicategory。
使われ方：Kerodon Corollary 5.6.0.6、straightening の図式の値との比較。 -/
noncomputable def leftFibrationInfinityFiberEvaluation {B : SSet.{u}} (b : B _⦋0⦌) :
    LeftFibrationInfinity B ⟶ SpaceInfinity.{u} :=
  coherentNerveMap (leftFibrationFiberEvaluationEnriched b)

/-- 概要：coherent な fiber 評価の対象での値は実際の Kan fiber の標準頂点。
方針：coherent nerve の後合成の頂点公式を適用する。
規約：束縛した left fibration p の標準頂点を入力する。
使われ方：Kerodon Corollary 5.6.0.6、fiber の豊穣評価と ∞ 圏の評価の接続。 -/
lemma leftFibrationInfinityFiberEvaluation_vertex {B : SSet.{u}} (b : B _⦋0⦌)
    (p : LeftFibrationObject B) :
    (leftFibrationInfinityFiberEvaluation b).app (Opposite.op ⦋0⦌) (coherentNerveVertex p) =
      coherentNerveVertex (leftFibrationFiberObject b p) :=
  coherentNerveMap_vertex (leftFibrationFiberEvaluationEnriched b) p

/-- 概要：fiber 評価の写像空間への作用は、相対 Hom の fiber への制限と coherent Hom 比較で可換。
方針：豊穣評価へ coherent Hom 比較の全次数の自然性を適用する。
規約：相対 Hom と内部 Hom の双方を u+1 へ持ち上げる。
使われ方：Kerodon Construction 4.6.7.3、Corollary 5.6.0.6、straightening の値での写像空間比較。 -/
lemma leftFibrationFiberEvaluation_mapping_naturality {B : SSet.{u}} (b : B _⦋0⦌)
    (p q : LeftFibrationObject B) :
    coherentHomComparison p q ≫ coherentPinchedHomMap (leftFibrationFiberEvaluationEnriched b) p q =
      (SSet.uliftFunctor.{u + 1, u}).map (relativeFunctorFiberHom p.val.hom q.val.hom b) ≫
        coherentHomComparison (leftFibrationFiberObject b p) (leftFibrationFiberObject b q) :=
  coherentHomComparison_enriched_naturality (leftFibrationFiberEvaluationEnriched b) p q

end SerrePositivity.InfinityCategories
