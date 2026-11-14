module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeSimplexComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictModuleCoherentFamily
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeLabelCoordinates

/-!
概要：元の native 余錐の旧頂点と成分を、元の閉零射列の同じ成分へ比較する。
方針：元の最後の頂点の置換の比較と、元の全 HA 自然変換の成分を使う。
規約：最後の頂点へ届く成分は別に native 列で比較する。
使われ方：3b-3 R6、元の指定余錐の旧成分の全 HA 可換式。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

private lemma cycleValueHEq {A : Type u} [CommRing A] {E : Type v} [DGCategory A E]
    {x y x' y' : E} (hx : x = x') (hy : y = y')
    (f : zeroCycles (homObject A E x y)) (g : zeroCycles (homObject A E x' y'))
    (h : HEq f g) : HEq f.val g.val := by
  cases hx
  cases hy
  cases eq_of_heq h
  rfl

variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 旧頂点の成分の斉次元は、元の同じ自然変換成分の斉次元と一致する。 -/
lemma strictBarNativeSimplexApp_castSucc_val_heq {F G : J ⥤ ModuleCategory A PUnit.{1}}
    (η : F ⟶ G) {n : ℕ} (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (i : Fin (n + 1)) :
    HEq (strictBarNativeSimplexApp A J η s i.castSucc).val
      (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (η.app (s.down.obj i))).val :=
  cycleValueHEq (A := A) (E := RightModule A PUnit.{1}) (strictBarNativeSimplex_obj_castSucc A J F s i)
    (strictBarNativeSimplex_obj_castSucc A J G s i) _ _
    (strictBarNativeSimplexApp_castSucc_heq A J η s i)

/-- apex の成分の斉次元は、同じ正規化 bar の射の斉次元と一致する。 -/
lemma strictBarNativeSimplexApp_last_val_heq {F G : J ⥤ ModuleCategory A PUnit.{1}}
    (η : F ⟶ G) {n : ℕ} (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    HEq (strictBarNativeSimplexApp A J η s (Fin.last (n + 1))).val
      (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (strictBarNormalizedMap A J η)).val :=
  cycleValueHEq (A := A) (E := RightModule A PUnit.{1})
    (dgCoherentBarNativeSimplex_last A PUnit.{1} (smallStrictBarDiagram A F)
      (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s)
    (dgCoherentBarNativeSimplex_last A PUnit.{1} (smallStrictBarDiagram A G)
      (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A G)) s) _ _
    (strictBarNativeSimplexApp_last_heq A J η s)

/-- 元の Bianchi データの旧射列。元の最後の対象を一度反復する。 -/
def strictBarOldChain (F : J ⥤ ModuleCategory A PUnit.{1}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    Fin (n + 2) ⥤ ModuleCategory A PUnit.{1} :=
  (Fin.last n).predAboveOrderHom.monotone.functor ⋙ s.down ⋙ F

/-- 元の Bianchi 単体は、元の同じ閉零射列の単体である。 -/
lemma strictBarBianchiOld_eq (F : J ⥤ ModuleCategory A PUnit.{1}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    dgCoherentBarBianchiOld A PUnit.{1} (smallStrictBarDiagram A F) s =
      closedNerveSimplex (A := A) (D := RightModule A PUnit.{1}) (strictBarOldChain A J F s) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveSimplex_pullback (A := A) (D := RightModule A PUnit.{1}) (s.down ⋙ F) (Fin.last n).predAboveOrderHom).symm

/-- 最後の頂点以外の native 対象は、元の同じ旧閉零射列の対象。 -/
lemma strictBarNativeOldObj (F : J ⥤ ModuleCategory A PUnit.{1}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (i : Fin (n + 2)) (hi : i ≠ Fin.last (n + 1)) :
    (strictBarNativeSimplex A J F s).obj i =
      ForgetEnrichment.to (Complex A) ((strictBarOldChain A J F s).obj i) := by
  induction i using Fin.lastCases with
  | last => exact (hi rfl).elim
  | cast j =>
    change (strictBarNativeSimplex A J F s).obj j.castSucc =
      ForgetEnrichment.to (Complex A)
        (F.obj (s.down.obj ((Fin.last n).predAboveOrderHom j.castSucc)))
    have he : (Fin.last n).predAboveOrderHom j.castSucc = j := Fin.predAbove_last_castSucc
    exact (strictBarNativeSimplex_obj_castSucc A J F s j).trans
      (congrArg (fun i => ForgetEnrichment.to (Complex A) (F.obj (s.down.obj i))) he.symm)

/-- 旧頂点の成分は、元の反復した閉零射列の同じ自然変換の成分。 -/
lemma strictBarNativeOldApp {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (i : Fin (n + 2)) (hi : i ≠ Fin.last (n + 1)) :
    HEq (strictBarNativeSimplexApp A J η s i).val
      (closedHomEquiv A (RightModule A PUnit.{1}) _ _
        ((Functor.whiskerLeft ((Fin.last n).predAboveOrderHom.monotone.functor ⋙ s.down) η).app i)).val := by
  induction i using Fin.lastCases with
  | last => exact (hi rfl).elim
  | cast j =>
    change HEq (strictBarNativeSimplexApp A J η s j.castSucc).val
      (closedHomEquiv A (RightModule A PUnit.{1}) _ _
        (η.app (s.down.obj ((Fin.last n).predAboveOrderHom j.castSucc)))).val
    have he : (Fin.last n).predAboveOrderHom j.castSucc = j := Fin.predAbove_last_castSucc
    have hh : ∀ (a b : Fin (n + 1)), a = b →
        HEq (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (η.app (s.down.obj a))).val
          (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (η.app (s.down.obj b))).val := by
      intro a b h
      cases h
      rfl
    exact (strictBarNativeSimplexApp_castSucc_val_heq A J η s j).trans (hh _ _ he.symm)

/-- 最後へ届かない元の native 成分は、元の旧閉零射列の同じ成分。 -/
lemma strictBarNativeOldHom (F : J ⥤ ModuleCategory A PUnit.{1}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (T : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ)
    (hT : 2 ≤ T.card) (ha : a = T.min' (Index.nonempty hT))
    (hb : b = T.max' (Index.nonempty hT)) (hk : k = 2 - (T.card : ℤ))
    (hbl : b ≠ Fin.last (n + 1)) :
    HEq ((strictBarNativeSimplex A J F s).hom T a b k hT ha hb hk)
      ((closedNerveData (strictBarOldChain A J F s)).hom T a b k hT ha hb hk) := by
  have h1 := dgCoherentBarPostLastData_hom_old
    (dgCoherentBarBianchiData A PUnit.{1} (smallStrictBarDiagram A F) s)
    (dgCoherentBarNormalizedModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F))
    (dgCoherentBarNativeBianchiProjection A PUnit.{1} (smallStrictBarDiagram A F)
      (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s)
    T a b k hT ha hb hk hbl
  have h2 := lastReplacement_hom_old
    (dgCoherentBarBianchiOld A PUnit.{1} (smallStrictBarDiagram A F) s).toSimplexData
    (ForgetEnrichment.to (Complex A) (dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)))
    (dgCoherentBarBianchiEndHom A PUnit.{1} (smallStrictBarDiagram A F) s)
    T a b k hT ha hb hk hbl
  have he : HEq
      ((dgCoherentBarBianchiOld A PUnit.{1} (smallStrictBarDiagram A F) s).hom T a b k hT ha hb hk)
      ((closedNerveData (strictBarOldChain A J F s)).hom T a b k hT ha hb hk) := by
    rw [strictBarBianchiOld_eq]
    rfl
  exact h1.trans (h2.trans he)

/-- 元の native 余錐の旧成分は、元の同じ全閉零自然変換に厳密に可換する。 -/
lemma strictBarNativeOld_naturality {F G : J ⥤ ModuleCategory A PUnit.{1}}
    (η : F ⟶ G) {n : ℕ} (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (T : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ)
    (hT : 2 ≤ T.card) (ha : a = T.min' (Index.nonempty hT))
    (hb : b = T.max' (Index.nonempty hT)) (hk : k = 2 - (T.card : ℤ))
    (hbl : b ≠ Fin.last (n + 1)) :
    compose A (strictBarNativeSimplexApp A J η s b).val
        ((strictBarNativeSimplex A J F s).hom T a b k hT ha hb hk) (add_zero k) =
      compose A ((strictBarNativeSimplex A J G s).hom T a b k hT ha hb hk)
        (strictBarNativeSimplexApp A J η s a).val (zero_add k) := by
  have hab : a ≤ b := by
    rw [ha, hb]
    exact (T.isLeast_min' _).2 (T.max'_mem _)
  have hal : a ≠ Fin.last (n + 1) := by
    intro h
    apply hbl
    apply le_antisymm (Fin.le_last b)
    simpa only [h] using hab
  let ηold := Functor.whiskerLeft ((Fin.last n).predAboveOrderHom.monotone.functor ⋙ s.down) η
  have hl := gradedHom_compose_heq (A := A) (D := RightModule A PUnit.{1})
    (strictBarNativeOldObj A J F s a hal) (strictBarNativeOldObj A J F s b hbl)
    (strictBarNativeOldObj A J G s b hbl) rfl rfl rfl
    (strictBarNativeSimplexApp A J η s b).val
    ((strictBarNativeSimplex A J F s).hom T a b k hT ha hb hk)
    (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (ηold.app b)).val
    ((closedNerveData (strictBarOldChain A J F s)).hom T a b k hT ha hb hk)
    (strictBarNativeOldApp A J η s b hbl) (strictBarNativeOldHom A J F s T a b k hT ha hb hk hbl)
    (add_zero k) (add_zero k)
  have hr := gradedHom_compose_heq (A := A) (D := RightModule A PUnit.{1})
    (strictBarNativeOldObj A J F s a hal) (strictBarNativeOldObj A J G s a hal)
    (strictBarNativeOldObj A J G s b hbl) rfl rfl rfl
    ((strictBarNativeSimplex A J G s).hom T a b k hT ha hb hk)
    (strictBarNativeSimplexApp A J η s a).val
    ((closedNerveData (strictBarOldChain A J G s)).hom T a b k hT ha hb hk)
    (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (ηold.app a)).val
    (strictBarNativeOldHom A J G s T a b k hT ha hb hk hbl) (strictBarNativeOldApp A J η s a hal)
    (zero_add k) (zero_add k)
  exact eq_of_heq (hl.trans ((heq_of_eq
    ((strictClosedSimplexMap (A := A) (E := RightModule A PUnit.{1}) ηold).naturality T a b k hT ha hb hk)).trans hr.symm))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
