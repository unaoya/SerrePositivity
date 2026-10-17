module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PrimitiveData
public import SerrePositivity.DifferentialGraded.Resolution.Cells.GeneratorBoundary
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain
public import SerrePositivity.DifferentialGraded.Functor.Components

/-! # 指定原始元による任意次数cell pathの評価 -/
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

/-- 既存HomをFで写し、生成cellを指定原始元へ写して順に合成する。 -/
def pathEvaluation : ∀ (w : List I) (x y : D),
    Cochain (C.term A D I w x y) (homObject A E (F.obj x) (F.obj y)) 0
  | [], x, y => Cochain.ofHom (F.map x y)
  | i :: w, x, y =>
    (tensorZeroCochain (Cochain.ofHom (F.map x (C.source i)))
      ((tensorZeroCochain (P.cochain i) (pathEvaluation w (C.target i) y)).comp
        (Cochain.ofHom (eComp (Complex A) (F.obj (C.source i))
          (F.obj (C.target i)) (F.obj y))) (zero_add 0))).comp
      (Cochain.ofHom (eComp (Complex A) (F.obj x)
        (F.obj (C.source i)) (F.obj y))) (zero_add 0)

lemma pathEvaluation_nil (x y : D) :
    P.pathEvaluation [] x y = Cochain.ofHom (F.map x y) := rfl

lemma pathEvaluation_cons_generator (i : I) (w : List I) (x y : D)
    (p q b n : ℤ) (hb : C.degree i + q = b) (hn : p + b = n)
    (f : (homObject A D x (C.source i)).X p)
    (t : (C.term A D I w (C.target i) y).X q) :
    (P.pathEvaluation (i :: w) x y).v n n (add_zero n)
      (ιTensorObj (homObject A D x (C.source i))
        (C.generator A D I i ⊗ C.term A D I w (C.target i) y) p b n hn
        (f ⊗ₜ[A] ιTensorObj (C.generator A D I i) (C.term A D I w (C.target i) y)
          (C.degree i) q b hb
          ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))) =
    forward A ((F.map x (C.source i)).f p f)
      (forward A (P.primitive i)
        ((P.pathEvaluation w (C.target i) y).v q q (add_zero q) t) hb) hn := by
  subst hb
  change ((tensorZeroCochain (Cochain.ofHom (F.map x (C.source i)))
      ((tensorZeroCochain (P.cochain i) (P.pathEvaluation w (C.target i) y)).comp
        (Cochain.ofHom (eComp (Complex A) (F.obj (C.source i))
          (F.obj (C.target i)) (F.obj y))) (zero_add 0))).comp
      (Cochain.ofHom (eComp (Complex A) (F.obj x)
        (F.obj (C.source i)) (F.obj y))) (zero_add 0)).v n n (add_zero n)
      (ιTensorObj (homObject A D x (C.source i))
        (C.generator A D I i ⊗ C.term A D I w (C.target i) y) p (C.degree i + q) n hn
        (f ⊗ₜ[A] ιTensorObj (C.generator A D I i) (C.term A D I w (C.target i) y)
          (C.degree i) q (C.degree i + q) rfl
          ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))) = _
  rw [cochain_comp_ofHom_apply, tensorZeroCochain_apply,
    cochain_comp_ofHom_apply, tensorZeroCochain_apply, cochain_generator]
  rfl

/-- 両側に単位を持つ一生成元pathの評価は指定原始元そのもの。 -/
lemma pathEvaluation_generatorTerm (i : I) :
    (P.pathEvaluation [i] (C.source i) (C.target i)).v
      (C.degree i) (C.degree i) (add_zero _)
      ((C.generatorTerm A D I i).f (C.degree i)
        ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))) =
    P.primitive i := by
  have he := congrArg (fun t : (C.term A D I [i] (C.source i) (C.target i)).X (C.degree i) =>
    (P.pathEvaluation [i] (C.source i) (C.target i)).v (C.degree i) (C.degree i) (add_zero _) t)
    (C.generatorTerm_apply A D I i
      ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)))
  have h := P.pathEvaluation_cons_generator i [] (C.source i) (C.target i)
    0 0 (C.degree i) (C.degree i) (add_zero _) (zero_add _)
      (unitElement A (C.source i)).val
      (unitElement A (C.target i)).val
  simp only [Family.term_nil, pathEvaluation_nil, Cochain.ofHom_v,
    DGFunctor.map_unitElement, unit_forward, forward_unit] at h
  exact he.trans h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
