module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeOldComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SmallStrictNativeLabelSource

/-!
概要：元の native 余錐の apex へ届く全 HA 成分の厳密自然性を証明する。
方針：元のラベルの同じ先頭を確認し、同じ native 列の cycle 合成の可換式へ移す。
規約：元の頂点・列・高次成分を保持する。
使われ方：3b-3 R6、元の指定余錐の全 HA 写像の混合成分。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 元の旧頂点は、同じ混合成分ラベルの同じ源加群である。 -/
lemma strictBarNativeLabelObj (F : J ⥤ ModuleCategory A PUnit.{1}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (T : Finset (Fin (n + 2))) (a : Fin (n + 1)) (hT : 2 ≤ T.card)
    (ha : a.castSucc = T.min' (Index.nonempty hT))
    (hb : Fin.last (n + 1) = T.max' (Index.nonempty hT)) :
    (strictBarNativeSimplex A J F s).obj a.castSucc =
      dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F)
        (dgCoherentBarBianchiLabel s T hT hb) := by
  have h := smallStrictBianchiLabel_obj_zero s T a hT ha hb
  rw [smallStrictBarDiagram_source]
  exact (strictBarNativeSimplex_obj_castSucc A J F s a).trans
    (congrArg (fun j => ForgetEnrichment.to (Complex A) (F.obj j)) h.symm)

/-- 混合成分で使う源の射は、同じラベルの先頭の自然変換成分そのもの。 -/
lemma strictBarNativeLabelApp {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (T : Finset (Fin (n + 2))) (a : Fin (n + 1)) (hT : 2 ≤ T.card)
    (ha : a.castSucc = T.min' (Index.nonempty hT))
    (hb : Fin.last (n + 1) = T.max' (Index.nonempty hT)) :
    HEq (strictBarNativeSimplexApp A J η s a.castSucc).val
      (closedHomEquiv A (RightModule A PUnit.{1}) _ _
        (η.app ((dgCoherentBarBianchiLabel s T hT hb).2.down.obj 0))).val := by
  have h := smallStrictBianchiLabel_obj_zero s T a hT ha hb
  have hh : ∀ (i j : J), i = j →
      HEq (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (η.app i)).val
        (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (η.app j)).val := by
    intro i j hij
    cases hij
    rfl
  exact (strictBarNativeSimplexApp_castSucc_val_heq A J η s a).trans (hh _ _ h.symm)

/-- apex へ届く元の全 HA 成分は、元の同じ自然変換と正規化 bar の射に可換する。 -/
lemma strictBarNativeMixed_naturality {F G : J ⥤ ModuleCategory A PUnit.{1}}
    (η : F ⟶ G) {n : ℕ} (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (T : Finset (Fin (n + 2))) (a : Fin (n + 1)) (k : ℤ)
    (hT : 2 ≤ T.card) (ha : a.castSucc = T.min' (Index.nonempty hT))
    (hb : Fin.last (n + 1) = T.max' (Index.nonempty hT)) (hk : k = 2 - (T.card : ℤ)) :
    compose A (strictBarNativeSimplexApp A J η s (Fin.last (n + 1))).val
        ((strictBarNativeSimplex A J F s).hom T a.castSucc (Fin.last (n + 1)) k hT ha hb hk)
        (add_zero k) =
      compose A
        ((strictBarNativeSimplex A J G s).hom T a.castSucc (Fin.last (n + 1)) k hT ha hb hk)
        (strictBarNativeSimplexApp A J η s a.castSucc).val (zero_add k) := by
  let t := dgCoherentBarBianchiLabel s T hT hb
  have hd := dgCoherentBarBianchiLabel_degree s T hT hb k hk
  have hF := dgCoherentBarNativeSimplexData_last_hom_heq A PUnit.{1} (smallStrictBarDiagram A F)
    (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F))
    s T a.castSucc k hT ha hb hk
  have hG := dgCoherentBarNativeSimplexData_last_hom_heq A PUnit.{1} (smallStrictBarDiagram A G)
    (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A G))
    s T a.castSucc k hT ha hb hk
  have hoF := dgCoherentBarNativeSimplex_last A PUnit.{1} (smallStrictBarDiagram A F)
    (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s
  have hoG := dgCoherentBarNativeSimplex_last A PUnit.{1} (smallStrictBarDiagram A G)
    (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A G)) s
  have hl := gradedHom_compose_heq (A := A) (D := RightModule A PUnit.{1})
    (strictBarNativeLabelObj A J F s T a hT ha hb) hoF hoG hd rfl hd
    (strictBarNativeSimplexApp A J η s (Fin.last (n + 1))).val
    ((strictBarNativeSimplex A J F s).hom T a.castSucc (Fin.last (n + 1)) k hT ha hb hk)
    (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (strictBarNormalizedMap A J η)).val
    (dgCoherentBarNativeColumn A PUnit.{1} (smallStrictBarDiagram A F)
      (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) t)
    (strictBarNativeSimplexApp_last_val_heq A J η s) hF
    (add_zero k) (add_zero (-(t.1 : ℤ)))
  have hr := gradedHom_compose_heq (A := A) (D := RightModule A PUnit.{1})
    (strictBarNativeLabelObj A J F s T a hT ha hb)
    (strictBarNativeLabelObj A J G s T a hT ha hb) hoG rfl hd hd
    ((strictBarNativeSimplex A J G s).hom T a.castSucc (Fin.last (n + 1)) k hT ha hb hk)
    (strictBarNativeSimplexApp A J η s a.castSucc).val
    (dgCoherentBarNativeColumn A PUnit.{1} (smallStrictBarDiagram A G)
      (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A G)) t)
    (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (η.app (t.2.down.obj 0))).val
    hG (strictBarNativeLabelApp A J η s T a hT ha hb)
    (zero_add k) (zero_add (-(t.1 : ℤ)))
  exact eq_of_heq (hl.trans ((heq_of_eq (strictBarNativeColumn_cycle_naturality A J η t)).trans hr.symm))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
