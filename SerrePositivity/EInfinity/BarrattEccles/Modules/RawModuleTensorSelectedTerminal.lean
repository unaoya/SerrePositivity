module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorSelectedAtMaxImage

/-!
概要：元の終端まで届く選択 cochain は、同じ普遍単体の成分そのものである。
方針：元の終端尾が恒等となるとき、輸送後の実後合成の像を回収する。
規約：元の端点等式を異種等号で保持する。
使われ方：cone の終端を含む混合削除成分の共通座標。
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

lemma strictRawModuleTensorElementSelectedCochainAtMax_terminal {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hm : J.max' hJ = Fin.last n) :
    HEq (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk)
      ((strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk) := by
  have ht : ∀ (i : Fin (n + 1)) (h : i = Fin.last n)
      (v : GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i))) k),
      HEq ((eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last i))))).f k v) v := by
    intro i h v
    subst i
    simp only [homOfLE_refl, CategoryTheory.Functor.map_id]
    simp only [eHomWhiskerLeft_id]
    rfl

  exact (ht _ hm (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk)).symm.trans
    (heq_of_eq (strictRawModuleTensorElementSelectedCochainAtMax_image A X P Q c J k hJ hk))

lemma strictRawModuleTensorElementSelectedCochainAtMax_terminal_smul {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hm : J.max' hJ = Fin.last n) (r : ℤˣ) :
    HEq (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk)
      (r • (strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk) := by
  have he := strictRawModuleTensorElementSelectedCochainAtMax_terminal A X P Q c J k hJ hk hm
  have hs : ∀ (i j : Fin (n + 1)) (h : i = j)
      (a : GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i))) k)
      (b : GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj j))) k),
      HEq a b → HEq (r • a) (r • b) := by
    intro i j h a b hab
    subst j
    cases eq_of_heq hab
    rfl
  exact hs _ _ hm _ _ he

end SerrePositivity.EInfinity.BarrattEccles
