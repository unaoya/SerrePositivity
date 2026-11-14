module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorSelectedAtMaxImage
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementPinchedEvaluation
public import SerrePositivity.EInfinity.Modules.ClosedPostcomposition

/-!
概要：元の最大点付き選択 cochain の評価を、同じ大域 pinched 族の線形成分へ戻す。
方針：全評価の自然性・Hom 後合成の合成則・元の全単体評価式を使う。
規約：HA Construction 1.3.1.13、任意次数・非空部分集合・実評価射を保持する。使われ方：大域評価三角形の混合項。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_evaluation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (J.max' hJ)))).f k
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) =
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n)))).f k
      ((strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk) := by
  rw [← strictRawModuleTensorElementSelectedCochainAtMax_image A X P Q c J k hJ hk]
  have hn := (strictRawModuleTensorElementEvaluation A X P Q).naturality
    (c.map (homOfLE (Fin.le_last (J.max' hJ))))
  have hn' : (strictRawModuleTensorElementDiagram A X P Q).map
      (c.map (homOfLE (Fin.le_last (J.max' hJ)))) ≫
        (strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n)) =
      (strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (J.max' hJ)) :=
    hn.trans (Category.comp_id _)
  have hf := ((eHomFunctor (Complex A) (strictRawModuleCategory A X)).obj (Opposite.op ((strictRawModuleProbeFunctor A X).obj P))).map_comp
    ((strictRawModuleTensorElementDiagram A X P Q).map
      (c.map (homOfLE (Fin.le_last (J.max' hJ)))))
    ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n)))
  change eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) (_ ≫ _) = _ at hf
  rw [hn'] at hf
  exact congrArg (fun f => f.f k
    (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk)) hf

lemma strictRawModuleTensorElementLinear_evaluation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (E := RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (x := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (x' := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
        ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n))))
      (strictRawModuleTensorElementLinear A X P Q c) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((strictRawModuleTensorElementPinchedMap A X P Q).app (Opposite.op ⦋n⦌) c) := by
  rw [strictRawModuleTensorElementPinchedMap_app]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear _ _).symm

lemma strictRawModuleTensorElementSelectedCochainAtMax_evaluation_pinched {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (J.max' hJ)))).f k
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
      ((strictRawModuleTensorElementPinchedMap A X P Q).app (Opposite.op ⦋n⦌) c)).val.component
        J k hJ hk := by
  have h := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (ForgetEnrichment.to (Complex A) Q) n => s.val.component J k hJ hk)
    (strictRawModuleTensorElementLinear_evaluation A X P Q c)
  exact (strictRawModuleTensorElementSelectedCochainAtMax_evaluation A X P Q c J k hJ hk).trans h

lemma strictRawModuleTensorElementSelectedCochainAtMax_evaluation_compose {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℤˣ) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (J.max' hJ)))).val
      (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) (add_zero k) =
    r • (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
      ((strictRawModuleTensorElementPinchedMap A X P Q).app (Opposite.op ⦋n⦌) c)).val.component
        J k hJ hk := by
  rw [modulePostcompose_graded]
  simp only [Units.smul_def, map_zsmul,
    strictRawModuleTensorElementSelectedCochainAtMax_evaluation_pinched A X P Q c J k hJ hk]

end SerrePositivity.EInfinity.BarrattEccles
