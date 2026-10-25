module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairUnitUnstraightening
public import SerrePositivity.InfinityCategories.F1.Coherent.UnstraighteningMappingEquivalence
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningParametrizedTransport
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPointFiberEvaluation

/-!
概要：空間値の全自然変換を、元の unstraightening の指定始対象の同じ pointed 像で評価する。
方針：元の全変換空間比較と始対象での相対評価を、標準 fiber 同型で移す。
規約：非可逆変換と全高次パラメータを保持する。
使われ方：同じ単位点での評価を元の関手の実 Hom 作用に接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：元の unstraightening の指定点の同じ pointed-space fiber での像。
方針：元の標準 fiber 同型の順方向に同じ点を送る。
規約：評価点を別に選択しない。
使われ方：全変換空間の評価と普遍輸送の同じ始点。 -/
def pairTransformationPoint {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u})
    (b : B _⦋0⦌) (z : (vertexFiber (leftUnstraighteningProjection F) b) _⦋0⦌) :
    (vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) b)) _⦋0⦌ :=
  (leftUnstraighteningFiberIso F b).hom.app (Opposite.op ⦋0⦌) z

/-- 概要：全自然変換空間の同じ指定点での実際の評価。
方針：元の fiber Hom 作用を同じ pointed 始点で評価する。
規約：元の全変換の高次単体を保持する。
使われ方：実 Hom 作用に続ける同値評価。 -/
def pairTransformationEvaluation {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (b : B _⦋0⦌) (z : (vertexFiber (leftUnstraighteningProjection F) b) _⦋0⦌) :
    leftUnstraighteningTransformationSpace F G ⟶
      vertexFiber pointedSpaceProjection (G.app (Opposite.op ⦋0⦌) b) :=
  leftUnstraighteningMappingFiberHom F G b ≫ evaluateFunctorAt (pairTransformationPoint F b z)

/-- 概要：同じ pointed 評価は元の全相対関手空間の指定点評価そのもの。
方針：標準 fiber 同型の往復、前後合成の評価、同じ相対点評価の式を使う。
規約：評価する元の点を保持する。
使われ方：始対象での評価の同値性の移送。 -/
lemma pairTransformationEvaluation_eq {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (b : B _⦋0⦌) (z : (vertexFiber (leftUnstraighteningProjection F) b) _⦋0⦌) :
    pairTransformationEvaluation F G b z =
      leftUnstraighteningMappingSpaceMap F G ≫
        relativeFunctorEvaluate (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
          z.val ≫
        eqToHom (congrArg (vertexFiber (leftUnstraighteningProjection G))
          (z.property.trans (pinchedConstant_zero b))) ≫
        (leftUnstraighteningFiberIso G b).hom := by
  let w := pairTransformationPoint F b z
  have hw : (leftUnstraighteningFiberIso F b).inv.app (Opposite.op ⦋0⦌) w = z :=
    congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) z) (leftUnstraighteningFiberIso F b).hom_inv_id
  rw [pairTransformationEvaluation, leftUnstraighteningMappingFiberHom]
  simp only [Category.assoc]
  rw [evaluateFunctorAt_post]
  rw [← Category.assoc _ (evaluateFunctorAt (pairTransformationPoint F b z))
      (leftUnstraighteningFiberIso G b).hom, evaluateFunctorAt_pre, hw]
  have h := congrArg (fun k ↦ leftUnstraighteningMappingSpaceMap F G ≫ k ≫
    (leftUnstraighteningFiberIso G b).hom)
    (relativeFunctorFiberHom_evaluate (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection G) b z)
  simpa only [Category.assoc] using h

/-- 概要：元の unstraightening の指定点が始対象なら同じ全変換空間の評価は同値。
方針：元の全変換空間比較と始対象での相対評価の自明 Kan 性に両端の同型を続ける。
規約：同じ元の評価射についての結論。
使われ方：実 Hom 作用の充満忠実性を同じ単位評価から検出する。 -/
lemma pairTransformationEvaluation_isQCatEquivalence {B : SSet.{u + 1}} [Quasicategory B]
    (F G : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
    (z : (vertexFiber (leftUnstraighteningProjection F) b) _⦋0⦌)
    (hz : IsInitialVertex z.val) : IsQCatEquivalence (pairTransformationEvaluation F G b z) := by
  rw [pairTransformationEvaluation_eq]
  have h₁ := leftUnstraighteningMappingSpaceMap_isQCatEquivalence F G
  have : TrivialKanFibration
      (relativeFunctorEvaluate (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
        z.val) := relativeFunctorEvaluate_initial_trivialKanFibration
    (leftUnstraighteningProjection G) (leftUnstraighteningProjection F) z.val hz
  have h₂ := isQCatEquivalence_of_trivialKanFibration
    (relativeFunctorEvaluate (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
      z.val)
  have h₃ := (qCatEquivalenceOfIso (eqToIso
    (congrArg (vertexFiber (leftUnstraighteningProjection G))
      (z.property.trans (pinchedConstant_zero b))))).isQCatEquivalence
  have h₄ := (qCatEquivalenceOfIso (leftUnstraighteningFiberIso G b)).isQCatEquivalence
  exact h₁.comp (h₂.comp (h₃.comp h₄))

/-- 概要：同じ指定点の評価は、実際の評価後の普遍輸送と全パラメータで関手同型。
方針：元の fiber Hom の輸送比較を同じ指定点の評価で後合成する。
規約：元の非可逆変換と同じ始点を保持する。
使われ方：実関手の Hom 作用後の評価と単位輸送の可換性。 -/
def pairTransformationEvaluation_parametrizedIso {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
    (z : (vertexFiber (leftUnstraighteningProjection F) b) _⦋0⦌) :
    FunctorIso (pairTransformationEvaluation F G b z)
      (intervalMappingPostOfEq (evaluateFunctorAt b) (functorVertex F) (functorVertex G)
          (evaluateFunctorAt_functorVertex _ _) (evaluateFunctorAt_functorVertex _ _) ≫
        parametrizedFiberTransport pointedSpaceProjection (F.app _ b) (G.app _ b) ≫
        evaluateFunctorAt (pairTransformationPoint F b z)) := by
  have h := (leftUnstraighteningMappingFiberHom_parametrizedIso F G b).postcomp
    (evaluateFunctorAt (pairTransformationPoint F b z))
  simpa only [pairTransformationEvaluation, Category.assoc] using h

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
