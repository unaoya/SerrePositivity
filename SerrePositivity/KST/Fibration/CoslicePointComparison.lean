module
public import SerrePositivity.InfinityCategories.F1.LeftFibrationCoslicePointFamily
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.F1.LiftEndpoint

/-! # 同じ coslice からの底上の全写像空間の比較を、元の恒等錐での評価へ戻す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌)

/-- 恒等錐での評価は、相対関手 ∞ 空間の全写像空間で充満忠実。 -/
theorem coslicePointEvaluation_fullyFaithful :
    IsFullyFaithful (leftFibrationCoslicePointEvaluate p b) := by
  have := leftFibrationCoslicePointEvaluate_trivialKanFibration p b
  exact (isQCatEquivalence_of_trivialKanFibration _).isFullyFaithful

/-- 元の実 fiber 点を全次数で固定した延長の空間は可縮な Kan 複体。 -/
theorem coslicePointExtension_isContractibleKan (v : (vertexFiber p b) _⦋0⦌) :
    IsContractibleKan (vertexFiber (leftFibrationCoslicePointEvaluate p b) v) := by
  have := leftFibrationCoslicePointEvaluate_trivialKanFibration p b
  exact vertexFiber_isContractibleKan _ _

/-- 同じ恒等錐の実 fiber 内の比較を、底を固定した相対関手空間内へ戻す。 -/
def coslicePointEvaluation_relativeIso
    {f g : sliceUnder (yonedaEquiv.symm b) ⟶ E}
    (hf : f ≫ p = sliceUnderProjection (yonedaEquiv.symm b))
    (hg : g ≫ p = sliceUnderProjection (yonedaEquiv.symm b))
    (e : VertexIso
      ((leftFibrationCoslicePointEvaluate p b).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex p _ f hf))
      ((leftFibrationCoslicePointEvaluate p b).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex p _ g hg))) :
    VertexIso (relativeFunctorVertex p _ f hf) (relativeFunctorVertex p _ g hg) :=
  (coslicePointEvaluation_fullyFaithful p b).preimageVertexIso e

/-- 恒等錐での同じ実比較は、元の二つの全 coslice 写像の自然同型を与える。 -/
def coslicePointEvaluation_functorIso
    {f g : sliceUnder (yonedaEquiv.symm b) ⟶ E}
    (hf : f ≫ p = sliceUnderProjection (yonedaEquiv.symm b))
    (hg : g ≫ p = sliceUnderProjection (yonedaEquiv.symm b))
    (e : VertexIso
      ((leftFibrationCoslicePointEvaluate p b).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex p _ f hf))
      ((leftFibrationCoslicePointEvaluate p b).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex p _ g hg))) : FunctorIso f g :=
  VertexIso.map (coslicePointEvaluation_relativeIso p b hf hg e)
    (vertexFiberι ((ihom (sliceUnder (yonedaEquiv.symm b))).map p)
      (functorVertex (sliceUnderProjection (yonedaEquiv.symm b))))

omit [Quasicategory B] [LeftFibration p] in
/-- 正規化済みの相対評価の元の全空間での値は、同じ写像の恒等錐での実際の評価。 -/
theorem coslicePointEvaluation_vertex_val
    {f : sliceUnder (yonedaEquiv.symm b) ⟶ E}
    (hf : f ≫ p = sliceUnderProjection (yonedaEquiv.symm b)) :
    ((leftFibrationCoslicePointEvaluate p b).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex p _ f hf)).val =
      f.app (Opposite.op ⦋0⦌) (cosliceIdentityCone b) := by
  have ht : leftFibrationCoslicePointEvaluate p b ≫ vertexFiberι p b =
      relativeFunctorEvaluate p (sliceUnderProjection (yonedaEquiv.symm b))
        (cosliceIdentityCone b) ≫ vertexFiberι p
          ((sliceUnderProjection (yonedaEquiv.symm b)).app (Opposite.op ⦋0⦌)
            (cosliceIdentityCone b)) := by
    rw [leftFibrationCoslicePointEvaluate, Category.assoc, vertexFiberTransport_ι]
    exact cosliceIdentityCone_projection b
  rw [relativeFunctorEvaluate_ι] at ht
  have hh := congrArg (fun m => m.app (Opposite.op ⦋0⦌)
    (relativeFunctorVertex p _ f hf)) ht
  exact hh.trans (evaluateFunctorAt_functorVertex (cosliceIdentityCone b) f)

end SerrePositivity.KST.Fibration
