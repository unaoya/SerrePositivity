module

public import SerrePositivity.InfinityCategories.F1.SubterminalFiber
public import SerrePositivity.InfinityCategories.F1.LeftFibrationFiberEvaluation
public import SerrePositivity.InfinityCategories.F1.CoherentNerveFullyFaithful

/-!
概要：一点を底とする相対 Hom と fiber 間の内部 Hom の厳密な同型。
方針：相対条件を消去した後、始域と標的の fiber 同型を内部 Hom に適用する。
規約：より一般に、指定頂点を持ち各次数で高々一点の底を扱う。
使われ方：Kerodon Corollary 5.6.0.6、fiber 評価による写像空間比較の一点上の基礎。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：一点を底とする相対関手空間は、その fiber 間の内部 Hom と同型。
方針：内部 Hom への fiber の包含と、始域・標的の fiber 同型による前合成・後合成を組み合わせる。
規約：射影 p と q に充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6、fiber の評価の写像空間上の比較。 -/
def relativeFunctorSubterminalBaseIso {E F B : SSet.{u}}
    [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)]
    (p : E ⟶ B) (q : F ⟶ B) (b : B _⦋0⦌) :
    relativeFunctorSpace q p ≅ (ihom (vertexFiber p b)).obj (vertexFiber q b) :=
  vertexFiberSubterminalBaseIso ((ihom E).map q) (functorVertex p) ≪≫
    ((internalHom (C := SSet.{u})).mapIso (vertexFiberSubterminalBaseIso p b).op).app F ≪≫
    (ihom (vertexFiber p b)).mapIso (vertexFiberSubterminalBaseIso q b).symm

/-- 概要：一点上の相対 Hom の同型の順方向は、既存の fiber 評価の射そのもの。
方針：内部 Hom の各パラメーターで、評価の後の fiber の部分型の値を計算する。
規約：同値類の比較ではなく、全次数の射の等式。
使われ方：Kerodon Corollary 5.6.0.6、実際の比較射の同型性の検証。 -/
lemma relativeFunctorSubterminalBaseIso_hom {E F B : SSet.{u}}
    [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)]
    (p : E ⟶ B) (q : F ⟶ B) (b : B _⦋0⦌) :
    (relativeFunctorSubterminalBaseIso p q b).hom = relativeFunctorFiberHom p q b := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  rfl

/-- 概要：一点を底とする相対 Hom の fiber への評価は同型。
方針：厳密に構成した同型の順方向との等式を用いる。
規約：射影の left fibration 性は不要。
使われ方：Kerodon Corollary 5.6.0.6、fiber 評価の全次数の充満忠実性。 -/
instance relativeFunctorFiberHom_isIso_of_subterminal {E F B : SSet.{u}}
    [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)]
    (p : E ⟶ B) (q : F ⟶ B) (b : B _⦋0⦌) : IsIso (relativeFunctorFiberHom p q b) := by
  rw [← relativeFunctorSubterminalBaseIso_hom]
  infer_instance

/-- 概要：一点を底とする left fibrations の ∞ 圏の fiber 評価は充満忠実。
方針：豊穣 Hom での厳密な同型性を coherent nerve の充満忠実性へ移す。
規約：𝒮 値の fiber 評価関手自体の写像空間上の主張。
使われ方：Kerodon Corollary 5.6.0.6、straightening の写像空間の比較の一点上の検証。 -/
lemma leftFibrationInfinityFiberEvaluation_isFullyFaithful_of_subterminal
    {B : SSet.{u}} [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (b : B _⦋0⦌) :
    IsFullyFaithful (leftFibrationInfinityFiberEvaluation b) := by
  apply (coherentNerveMap_isFullyFaithful_iff (leftFibrationFiberEvaluationEnriched b)).mpr
  intro p q
  change IsQCatEquivalence (relativeFunctorFiberHom p.val.hom q.val.hom b)
  rw [← relativeFunctorSubterminalBaseIso_hom]
  exact (qCatEquivalenceOfIso
    (relativeFunctorSubterminalBaseIso p.val.hom q.val.hom b)).isQCatEquivalence

end SerrePositivity.InfinityCategories
