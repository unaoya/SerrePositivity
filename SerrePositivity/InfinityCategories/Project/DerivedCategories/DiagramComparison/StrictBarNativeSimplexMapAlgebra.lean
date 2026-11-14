module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeSimplexMap

/-!
概要：元の native 余錐の HA 写像が、元の自然変換の恒等と合成を保つことを示す。
方針：同じ頂点成分を比較し、閉零射の恒等・合成と同じ bar 関手則へ戻す。
規約：対象ごとの写像の選択を追加しない。
使われ方：3b-3 R6、元の指定余錐の全パラメーターの族。
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

private lemma cycleAlongEq_unit {A : Type u} [CommRing A] {E : Type (u + 1)} [DGCategory A E]
    {x x' : E} (hx : x = x') :
    strictBarCycleAlongEq (A := A) (E := E) hx hx (unitElement A x) = unitElement A x' := by
  cases hx
  rfl

private lemma cycleAlongEq_comp {A : Type u} [CommRing A] {E : Type (u + 1)} [DGCategory A E]
    {x y z x' y' z' : E} (hx : x = x') (hy : y = y') (hz : z = z')
    (f : zeroCycles (homObject A E x y)) (g : zeroCycles (homObject A E y z))
    (h : zeroCycles (homObject A E x z))
    (hc : h.val = compose A g.val f.val (zero_add 0)) :
    (strictBarCycleAlongEq (A := A) (E := E) hx hz h).val =
      compose A (strictBarCycleAlongEq (A := A) (E := E) hy hz g).val (strictBarCycleAlongEq (A := A) (E := E) hx hy f).val
        (zero_add 0) := by
  cases hx
  cases hy
  cases hz
  exact hc

variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 元の恒等自然変換は、元の native 余錐の同じ厳密恒等 HA 写像へ移る。 -/
lemma strictBarNativeSimplexMap_id (F : J ⥤ ModuleCategory A PUnit.{1}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    strictBarNativeSimplexMap A J (𝟙 F) s =
      StrictSimplexMap.id (strictBarNativeSimplex A J F s).toSimplexData := by
  apply StrictSimplexMap.ext
  intro i
  have hn : strictBarNormalizedMap A J (𝟙 F) = 𝟙 ((strictBarNormalizedFunctor A J).obj F) :=
    (strictBarNormalizedFunctor A J).map_id F
  induction i using Fin.lastCases with
  | last =>
    simp only [strictBarNativeSimplexMap, StrictSimplexMap.id, strictBarNativeSimplexApp,
      Fin.lastCases_last, hn, closedHom_id (A := A) (D := RightModule A PUnit.{1})]
    exact cycleAlongEq_unit (A := A) (E := RightModule A PUnit.{1}) _
  | cast j =>
    simp only [strictBarNativeSimplexMap, StrictSimplexMap.id, strictBarNativeSimplexApp,
      Fin.lastCases_castSucc, NatTrans.id_app, closedHom_id (A := A) (D := RightModule A PUnit.{1})]
    exact cycleAlongEq_unit (A := A) (E := RightModule A PUnit.{1}) _

/-- 元の自然変換の合成は、元の native 余錐の同じ厳密 HA 写像の合成へ移る。 -/
lemma strictBarNativeSimplexMap_comp {F G H : J ⥤ ModuleCategory A PUnit.{1}}
    (η : F ⟶ G) (θ : G ⟶ H) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    strictBarNativeSimplexMap A J (η ≫ θ) s =
      (strictBarNativeSimplexMap A J η s).comp (strictBarNativeSimplexMap A J θ s) := by
  apply StrictSimplexMap.ext
  intro i
  apply Subtype.ext
  have hn : strictBarNormalizedMap A J (η ≫ θ) =
      strictBarNormalizedMap A J η ≫ strictBarNormalizedMap A J θ :=
    (strictBarNormalizedFunctor A J).map_comp η θ
  induction i using Fin.lastCases with
  | last =>
    simp only [strictBarNativeSimplexMap, StrictSimplexMap.comp, strictBarNativeSimplexApp,
      Fin.lastCases_last]
    apply cycleAlongEq_comp (A := A) (E := RightModule A PUnit.{1})
    rw [hn]
    exact closedHom_comp (A := A) (D := RightModule A PUnit.{1}) _ _
  | cast j =>
    simp only [strictBarNativeSimplexMap, StrictSimplexMap.comp, strictBarNativeSimplexApp,
      Fin.lastCases_castSucc, NatTrans.comp_app]
    apply cycleAlongEq_comp (A := A) (E := RightModule A PUnit.{1})
    exact closedHom_comp (A := A) (D := RightModule A PUnit.{1}) _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
