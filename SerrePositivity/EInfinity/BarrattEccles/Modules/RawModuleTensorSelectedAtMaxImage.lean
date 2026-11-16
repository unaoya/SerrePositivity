module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementSelected

/-!
概要：最大点へ輸送した同じ選択 cochain の像を、元の列の同じ普遍成分に戻す。
方針：添字等式の輸送と後合成を両立させ、元の選択係数の像の定理を使う。
規約：元の最大点・終端尾・実 frame 射を保持する。
使われ方：実 cone の混合削除項と終端合成項の共通座標。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_image {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementDiagram A X P Q).map
      (c.map (homOfLE (Fin.le_last (J.max' hJ)))))).f k
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) =
    (strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk := by
  have ht : ∀ (i j : Fin (n + 1)) (h : i = j)
      (v : GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i))) k),
      (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last j))))).f k
        (cast (congrArg (fun z => (GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
          (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj z))) k : Type u)) h) v) =
      (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last i))))).f k v := by
    intro i j h v
    subst j
    rfl
  exact (ht _ _ (strictRawModuleTensorElementSelection_last J hJ)
    (strictRawModuleTensorElementSelectedCochain A X P Q c J k hJ hk)).trans
      (strictRawModuleTensorElementSelectedCochain_image A X P Q c J k hJ hk)

end SerrePositivity.EInfinity.BarrattEccles
