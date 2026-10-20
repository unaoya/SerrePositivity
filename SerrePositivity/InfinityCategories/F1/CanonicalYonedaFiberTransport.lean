module

public import SerrePositivity.InfinityCategories.F1.SmallUnstraighteningPointFiberEvaluation
public import SerrePositivity.InfinityCategories.F1.CoherentUnstraighteningMappingEquivalence
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningParametrizedTransport

/-!
概要：Tw 全体からの同じ恒等点による Yoneda 評価を、c1 の実際の普遍輸送へ接続する。
方針：相対 Hom と fiber の縮小同型の可換式で評価を移し、c1 の輸送比較を後合成する。
規約：全パラメーターでの厳密な等式と関手同型を区別して保持する。
使われ方：同じ Yoneda 写像の Hom 作用を、Tw の恒等点からの輸送として検出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 全体から取った同じ恒等点を、普遍 pointed-space 射影の実際の fiber の点として表示する。 -/
def canonicalYonedaPointedIdentity {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (vertexFiber pointedSpaceProjection
      ((representablePresheafInfinity y).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm y)))) _⦋0⦌ :=
  (leftUnstraighteningFiberIso (representablePresheafInfinity y)
      (ULift.up (SSet.opObjEquiv.symm y))).hom.app (Opposite.op ⦋0⦌)
    ((smallLeftUnstraighteningFiberIso (representablePresheafInfinity y)
      (SSet.opObjEquiv.symm y)).hom.app (Opposite.op ⦋0⦌)
        (ULift.up (canonicalYonedaIdentityFiber y)))

/-- c1 の実際の全変換空間の fiber 作用を、同じ全体からの恒等点で評価する。 -/
def canonicalYonedaTransformationFiberEvaluation {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌) (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    leftUnstraighteningTransformationSpace (representablePresheafInfinity y) F ⟶
      vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm y))) :=
  leftUnstraighteningMappingFiberHom (representablePresheafInfinity y) F
      (ULift.up (SSet.opObjEquiv.symm y)) ≫ evaluateFunctorAt (canonicalYonedaPointedIdentity y)

/-- 同じ指定点での c1 の評価は、小さい相対 Hom の恒等点評価の移送そのもの。 -/
lemma canonicalYonedaTransformationFiberEvaluation_eq
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    canonicalYonedaTransformationFiberEvaluation y F =
    leftUnstraighteningMappingSpaceMap (representablePresheafInfinity y) F ≫
      (smallLeftUnstraighteningRelativeFunctorIso (representablePresheafInfinity y) F).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (canonicalYonedaUnstraighteningEvaluation (smallLeftUnstraighteningProjection F) y) ≫
      (smallLeftUnstraighteningFiberIso F (SSet.opObjEquiv.symm y)).hom ≫
      (leftUnstraighteningFiberIso F (ULift.up (SSet.opObjEquiv.symm y))).hom := by
  let R := representablePresheafInfinity y
  let b := SSet.opObjEquiv.symm y
  let e := smallLeftUnstraighteningRelativeFunctorIso R F
  let v := canonicalYonedaIdentityFiber y
  let w := (smallLeftUnstraighteningFiberIso R b).hom.app (Opposite.op ⦋0⦌) (ULift.up v)
  let z := canonicalYonedaPointedIdentity y
  have hz : (leftUnstraighteningFiberIso R (ULift.up b)).inv.app (Opposite.op ⦋0⦌) z = w :=
    congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) w)
      (leftUnstraighteningFiberIso R (ULift.up b)).hom_inv_id
  have hPoint := smallLeftUnstraighteningRelativeFunctorIso_pointEvaluation R F b v
  rw [← canonicalYonedaUnstraighteningEvaluation_eq_fiberEvaluation] at hPoint
  have hBig : relativeFunctorFiberHom (leftUnstraighteningProjection R)
      (leftUnstraighteningProjection F) (ULift.up b) ≫ evaluateFunctorAt w =
      e.inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
        (canonicalYonedaUnstraighteningEvaluation (smallLeftUnstraighteningProjection F) y) ≫
      (smallLeftUnstraighteningFiberIso F b).hom := by
    calc
      _ = e.inv ≫ (e.hom ≫ relativeFunctorFiberHom (leftUnstraighteningProjection R)
          (leftUnstraighteningProjection F) (ULift.up b) ≫ evaluateFunctorAt w) :=
        (e.inv_hom_id_assoc _).symm
      _ = _ := by rw [hPoint]
  rw [canonicalYonedaTransformationFiberEvaluation, leftUnstraighteningMappingFiberHom]
  simp only [Category.assoc]
  rw [evaluateFunctorAt_post]
  rw [← Category.assoc _ (evaluateFunctorAt z)
    (leftUnstraighteningFiberIso F (ULift.up b)).hom, evaluateFunctorAt_pre, hz]
  have h := congrArg (fun f ↦ leftUnstraighteningMappingSpaceMap R F ≫ f ≫
    (leftUnstraighteningFiberIso F (ULift.up b)).hom) hBig
  simpa only [Category.assoc] using h

/-- 全体からの同じ恒等点における、c1 の全変換空間の実際の評価は同値。 -/
lemma canonicalYonedaTransformationFiberEvaluation_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence (canonicalYonedaTransformationFiberEvaluation y F) := by
  rw [canonicalYonedaTransformationFiberEvaluation_eq]
  have h₁ := leftUnstraighteningMappingSpaceMap_isQCatEquivalence
    (representablePresheafInfinity y) F
  have h₂ := (qCatEquivalenceOfIso
    (smallLeftUnstraighteningRelativeFunctorIso
      (representablePresheafInfinity y) F).symm).isQCatEquivalence
  have h₃ := (canonicalYonedaUnstraighteningEvaluation_isQCatEquivalence
    (smallLeftUnstraighteningProjection F) y).ulift.{u, u + 1}
  have h₄ := (qCatEquivalenceOfIso
    (smallLeftUnstraighteningFiberIso F (SSet.opObjEquiv.symm y))).isQCatEquivalence
  have h₅ := (qCatEquivalenceOfIso
    (leftUnstraighteningFiberIso F (ULift.up (SSet.opObjEquiv.symm y)))).isQCatEquivalence
  exact h₁.comp (h₂.comp (h₃.comp (h₄.comp h₅)))

/-- 同じ全体からの恒等点評価は、評価した変換に沿う実際の普遍輸送の評価と関手同型。 -/
def canonicalYonedaTransformationFiberEvaluation_parametrizedIso
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    FunctorIso (canonicalYonedaTransformationFiberEvaluation y F)
      (intervalMappingPostOfEq (evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm y)))
          (functorVertex (representablePresheafInfinity y)) (functorVertex F)
          (evaluateFunctorAt_functorVertex _ _) (evaluateFunctorAt_functorVertex _ _) ≫
        parametrizedFiberTransport pointedSpaceProjection
          ((representablePresheafInfinity y).app _ (ULift.up (SSet.opObjEquiv.symm y)))
          (F.app _ (ULift.up (SSet.opObjEquiv.symm y))) ≫
        evaluateFunctorAt (canonicalYonedaPointedIdentity y)) := by
  have h := (leftUnstraighteningMappingFiberHom_parametrizedIso
    (representablePresheafInfinity y) F (ULift.up (SSet.opObjEquiv.symm y))).postcomp
      (evaluateFunctorAt (canonicalYonedaPointedIdentity y))
  simpa only [canonicalYonedaTransformationFiberEvaluation, Category.assoc] using h

end SerrePositivity.InfinityCategories
