module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryActionEvaluation

/-! # 前方Homと指定原始元による有限path評価作用 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w}
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

def evaluationOriginalAction (_P : PrimitiveData A D I C E F) (x t y : D) :
    homObject A D x t ⊗ homObject A E (F.obj t) (F.obj y) ⟶
      homObject A E (F.obj x) (F.obj y) :=
  (F.map x t ▷ homObject A E (F.obj t) (F.obj y)) ≫
    eComp (Complex A) (F.obj x) (F.obj t) (F.obj y)

def evaluationPrefixAction (i : I) (x y : D) :
    Cochain (homObject A D x (C.source i) ⊗
      (C.generator A D I i ⊗ homObject A E (F.obj (C.target i)) (F.obj y)))
      (homObject A E (F.obj x) (F.obj y)) 0 :=
  ((tensorLeftHom (homObject A D x (C.source i))
    (C.generator A D I i ⊗ homObject A E (F.obj (C.target i)) (F.obj y))
    (homObject A E (F.obj (C.source i)) (F.obj y))).f 0
      (P.primitiveAction i (F.obj y))).comp
    (Cochain.ofHom (P.evaluationOriginalAction x (C.source i) y)) (zero_add 0)

lemma evaluationPrefixAction_differential (i : I) (x y : D) :
    δ 0 1 (P.evaluationPrefixAction i x y) =
    ((tensorLeftHom (homObject A D x (C.source i))
      (C.generator A D I i ⊗ homObject A E (F.obj (C.target i)) (F.obj y))
      (homObject A E (F.obj (C.source i)) (F.obj y))).f 1
        (δ 0 1 (P.primitiveAction i (F.obj y)))).comp
      (Cochain.ofHom (P.evaluationOriginalAction x (C.source i) y)) (add_zero 1) := by
  rw [evaluationPrefixAction, δ_comp_ofHom,
    homComplexMap_differential (tensorLeftHom _ _ _) 0 1]

lemma pathEvaluation_cons_action (i : I) (w : List I) (x y : D) :
    P.pathEvaluation (i :: w) x y =
    ((tensorLeftHom (homObject A D x (C.source i))
      (C.generator A D I i ⊗ C.term A D I w (C.target i) y)
      (C.generator A D I i ⊗ homObject A E (F.obj (C.target i)) (F.obj y))).f 0
      ((tensorLeftHom (C.generator A D I i) (C.term A D I w (C.target i) y)
        (homObject A E (F.obj (C.target i)) (F.obj y))).f 0
          (P.pathEvaluation w (C.target i) y))).comp
      (P.evaluationPrefixAction i x y) (zero_add 0) := by
  change (tensorZeroCochain (Cochain.ofHom (F.map x (C.source i)))
      ((tensorZeroCochain (P.cochain i) (P.pathEvaluation w (C.target i) y)).comp
        (Cochain.ofHom (eComp (Complex A) (F.obj (C.source i))
          (F.obj (C.target i)) (F.obj y))) (zero_add 0))).comp
      (Cochain.ofHom (eComp (Complex A) (F.obj x)
        (F.obj (C.source i)) (F.obj y))) (zero_add 0) = _
  rw [primitiveAction_evaluate, tensorZeroCochain_ofHom_left, tensorLeftHom_cochain_comp]
  simp only [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  rfl

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
