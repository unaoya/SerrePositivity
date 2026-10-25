module

public import SerrePositivity.InfinityCategories.F1.Coherent.RepresentableHomFunctor
public import SerrePositivity.InfinityCategories.F1.Coherent.KanCosliceComparison
public import SerrePositivity.InfinityCategories.F1.Coherent.OrderDiagrams
public import SerrePositivity.InfinityCategories.Core.FunctorCompositionEvaluation
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedReverseFiberVertices

/-!
概要：豊穣 Hom の恒等射から作る全 coslice 比較の同値性。
方針：同じ比較の全 Hom 上の作用を、豊穣合成の左単位則で標準一点 Hom 同型へ戻す。
規約：大域射を先に固定し、各 fiber の別の値同値を貼り合わせない。
使われ方：HTT 5.1.3、表現可能関手の全 coherent 比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {D : Type (u + 1)} [Category.{u} D] [SimplicialCategory D]
  [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)] (x : D)

/-- 元の豊穣恒等射の零単体。 -/
def representableHomIdentity : (SimplicialCategory.sHom x x) _⦋0⦌ :=
  SSet.unitHomEquiv _ (eId SSet x)

/-- 同じ恒等射を反転した一点 Hom の係数として表示する。 -/
def representableHomIdentityCoefficient :
    (((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject
      ((representableHomFunctor x).obj x))).op) _⦋0⦌ :=
  SSet.opObjEquiv.symm (ULift.up
    (SimplicialCategory.homEquiv' pointKanObject ((representableHomFunctor x).obj x)
      (SSet.yonedaEquiv.symm (representableHomIdentity x))))

/-- 同じ恒等係数の pointed 頂点は、元の豊穣恒等射の零単体を回収する。 -/
lemma representableHomIdentityCoefficient_value :
    pointedSpaceFiberVertexEquiv ((representableHomFunctor x).obj x)
      (KanCosliceComparison.pointed (representableHomFunctor x) x
        (representableHomIdentityCoefficient x)) = representableHomIdentity x := by
  let K := (representableHomFunctor x).obj x
  let p : pointKanObject ⟶ K := SSet.yonedaEquiv.symm (representableHomIdentity x)
  have h := pointedReverseKanFiberComparison_vertex K p
  change pointedSpaceFiberVertexEquiv K
    ((pointedReverseKanFiberComparison K).app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (ULift.up (SimplicialCategory.homEquiv' pointKanObject K p)))) = _
  rw [h]
  exact SSet.yonedaEquiv.apply_symm_apply _

/-- 実際の全空間比較の始点 fiber を表示し直すと、同じ恒等射を厳密に回収する。 -/
lemma representableHomCosliceIdentity_value :
    pointedSpaceFiberVertexEquiv ((representableHomFunctor x).obj x)
      ((KanCosliceComparison.fiberIso (representableHomFunctor x) x).hom.app
        (Opposite.op ⦋0⦌) (KanCosliceComparison.start (representableHomFunctor x) x
          (representableHomIdentityCoefficient x))) = representableHomIdentity x := by
  rw [KanCosliceComparison.start_pointed]
  exact representableHomIdentityCoefficient_value x

/-- 恒等係数への同じ豊穣作用は標準一点 Hom 同型の逆射。 -/
lemma representableHomIdentityAction_eq (y : D) :
    KanCosliceComparison.action (representableHomFunctor x) x
      (representableHomIdentityCoefficient x) y =
    SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map
      (pointFunctorEvaluationIso (SimplicialCategory.sHom x y)).inv) := by
  let F := representableHomFunctor x
  let p : pointKanObject ⟶ F.obj x := SSet.yonedaEquiv.symm (representableHomIdentity x)
  have h : KanCosliceComparison.action F x (representableHomIdentityCoefficient x) y =
      SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map
        (F.map x y ≫ eHomWhiskerRight SSet p (F.obj y))) := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro a
    apply SSet.opObjEquiv.injective
    apply ULift.ext
    dsimp only [KanCosliceComparison.action, coherentReverseHomComposition,
      coherentReverseCompositionParameters, coherentHomComposition]
    simp only [eComp_op_eq]
    change (eComp SSet pointKanObject (F.obj x) (F.obj y)).app (Opposite.op ⦋n⦌)
      ((SSet.opObjEquiv (PinchedHom.constant (representableHomIdentityCoefficient x) n)).down,
        (F.map x y).app (Opposite.op ⦋n⦌) (SSet.opObjEquiv a).down) =
      (eComp SSet pointKanObject (F.obj x) (F.obj y)).app (Opposite.op ⦋n⦌)
        ((eHomEquiv SSet p).app (Opposite.op ⦋n⦌) PUnit.unit,
          (F.map x y).app (Opposite.op ⦋n⦌) (SSet.opObjEquiv a).down)
    congr 1
  rw [h]
  congr 1
  congr 1
  apply (cancel_mono (pointFunctorEvaluationIso (SimplicialCategory.sHom x y)).hom).1
  rw [Iso.inv_hom_id, Category.assoc]
  let p₀ : (Δ[0] : SSet.{u}) ⟶ SimplicialCategory.sHom x x := p
  have hp : eHomWhiskerRight SSet p (F.obj y) =
      (pre p₀).app (SimplicialCategory.sHom x y) := by
    change (λ_ _).inv ≫ curry' p₀ ▷ _ ≫ MonoidalClosed.comp _ _ _ = _
    rw [curry'_whiskerRight_comp, Iso.inv_hom_id_assoc]
    rfl
  rw [hp, pointFunctorEvaluationIso, evaluateFunctorAt_pre]
  have pv : p₀.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) =
      representableHomIdentity x := by
    have h₀ : (stdSimplex.obj₀Equiv.symm 0 : (Δ[0] : SSet.{u}) _⦋0⦌) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
      apply stdSimplex.ext
      intro i
      apply Fin.ext
      omega
    rw [h₀]
    exact SSet.yonedaEquiv_symm_app_id _
  rw [pv]
  change curry (eComp SSet x x y) ≫ evaluateFunctorAt
    (SSet.unitHomEquiv _ (eId SSet x)) = _
  rw [curry_evaluateFunctorAt_unitHomEquiv]
  exact e_id_comp SSet x y

/-- 恒等係数に作用する射は全ての標的で同値。 -/
lemma representableHomIdentityAction_isQCatEquivalence (y : D) :
    IsQCatEquivalence (KanCosliceComparison.action (representableHomFunctor x) x
      (representableHomIdentityCoefficient x) y) := by
  rw [representableHomIdentityAction_eq]
  exact (qCatEquivalenceOfIso
    (SSet.opFunctor.mapIso ((SSet.uliftFunctor.{u + 1, u}).mapIso
      (pointFunctorEvaluationIso (SimplicialCategory.sHom x y)).symm))).isQCatEquivalence

/-- 元の恒等射から作った全 coslice 比較は同値。 -/
lemma representableHomCosliceComparison_isQCatEquivalence :
    IsQCatEquivalence (KanCosliceComparison.map (representableHomFunctor x) x
      (representableHomIdentityCoefficient x)) :=
  KanCosliceComparison.isQCatEquivalence _ _ _ (representableHomIdentityAction_isQCatEquivalence x)

end SerrePositivity.InfinityCategories
