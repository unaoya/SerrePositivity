module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorSelectionCard

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementSelected

/-!
概要：選択 cochain を明示次数と濃度の等式で表示し、元の選択係数へ厳密に戻す。
方針：同じ列挙で選んだ全列の最上位普遍成分を、同じ最大点へ輸送する。
規約：元の実 cochain・最大点・次数を保つ。使われ方：像の列挙との同じ次数での比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementSelectedCochainAtMaxOfCard {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℕ) (hc : J.card = r + 1) :
    GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (J.max' hJ)))) k :=
  cast (congrArg (fun i => (GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
    (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i))) k : Type u))
      (normalizedTensorElementSelectionOfCard_last J r hc hJ))
    ((strictRawModuleTensorElementLinear A X P Q
      ((SimplexCategory.toCat.map
        (normalizedTensorElementSelectionOfCard J r hc)).toFunctor ⋙ c)).val.component
        Finset.univ k Finset.univ_nonempty
        (by simpa only [Finset.card_univ, Fintype.card_fin, ← hc] using hk))

lemma strictRawModuleTensorElementSelectedCochainAtMax_eq_ofCard {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk =
      strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c J k hJ hk (J.card - 1)
        (by have := Finset.card_pos.mpr hJ; omega) := rfl

lemma strictRawModuleTensorElementSelectedCochainAtMaxOfCard_congr {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r s : ℕ) (hrs : r = s) (hr : J.card = r + 1) (hs : J.card = s + 1) :
    strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c J k hJ hk r hr =
      strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c J k hJ hk s hs := by
  subst s
  rfl

lemma strictRawModuleTensorElementSelectedCochainAtMaxOfCard_raw {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℕ) (hc : J.card = r + 1) :
    HEq (strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c J k hJ hk r hc)
      ((strictRawModuleTensorElementLinear A X P Q
        ((SimplexCategory.toCat.map
          (normalizedTensorElementSelectionOfCard J r hc)).toFunctor ⋙ c)).val.component
            Finset.univ k Finset.univ_nonempty
            (by simpa only [Finset.card_univ, Fintype.card_fin, ← hc] using hk)) := by
  exact cast_heq _ _

end SerrePositivity.EInfinity.BarrattEccles
