module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeCycleNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeSimplices

/-!
概要：元の native 余錐の HA 単体間の同じ閉零頂点成分を構成する。
方針：旧頂点には元の自然変換、apex には同じ正規化 bar の射を使う。
規約：元の native 単体と対象を保持し、対象の等式による移送だけを行う。
使われ方：3b-3 R6、元の余錐の全 HA 写像の構成。
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

/-- 対象の等式に沿う閉零 cycle の同じ移送。 -/
def strictBarCycleAlongEq {A : Type u} [CommRing A] {E : Type (u + 1)} [DGCategory A E]
    {x y x' y' : E} (hx : x = x') (hy : y = y')
    (f : zeroCycles (homObject A E x y)) : zeroCycles (homObject A E x' y') := by
  cases hx
  cases hy
  exact f

/-- 同じ対象の等式によるcycle移送は、元のcycleを異種等号で保持する。 -/
lemma strictBarCycleAlongEq_heq {A : Type u} [CommRing A] {E : Type (u + 1)} [DGCategory A E]
    {x y x' y' : E} (hx : x = x') (hy : y = y')
    (f : zeroCycles (homObject A E x y)) : HEq (strictBarCycleAlongEq (A := A) (E := E) hx hy f) f := by
  cases hx
  cases hy
  rfl

variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 元の strict 図式から既存の構成で得た、同じ native 余錐の HA 単体。 -/
abbrev strictBarNativeSimplex (F : J ⥤ ModuleCategory A PUnit.{1}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :=
  dgCoherentBarNativeSimplex A PUnit.{1} (smallStrictBarDiagram A F)
    (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s

/-- 元の native 単体の旧頂点は、元の同じ係数加群である。 -/
lemma strictBarNativeSimplex_obj_castSucc (F : J ⥤ ModuleCategory A PUnit.{1}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) (i : Fin (n + 1)) :
    (strictBarNativeSimplex A J F s).obj i.castSucc =
      ForgetEnrichment.to (Complex A) (F.obj (s.down.obj i)) :=
  congrArg (fun t : Simplex A (RightModule A PUnit.{1}) n => t.obj i)
    (dgCoherentBarNativeSimplex_front A PUnit.{1} (smallStrictBarDiagram A F)
      (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s)

/-- 元の native 単体間で使う、元の自然変換と同じ bar の射の閉零成分。 -/
def strictBarNativeSimplexApp {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G)
    {n : ℕ} (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) (i : Fin (n + 2)) :
    zeroCycles (homObject A (RightModule A PUnit.{1})
      ((strictBarNativeSimplex A J F s).obj i) ((strictBarNativeSimplex A J G s).obj i)) :=
  Fin.lastCases
    (strictBarCycleAlongEq (A := A) (E := RightModule A PUnit.{1})
      (dgCoherentBarNativeSimplex_last A PUnit.{1} (smallStrictBarDiagram A F)
        (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s).symm
      (dgCoherentBarNativeSimplex_last A PUnit.{1} (smallStrictBarDiagram A G)
        (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A G)) s).symm
      (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (strictBarNormalizedMap A J η)))
    (fun j => strictBarCycleAlongEq (A := A) (E := RightModule A PUnit.{1}) (strictBarNativeSimplex_obj_castSucc A J F s j).symm
      (strictBarNativeSimplex_obj_castSucc A J G s j).symm
      (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (η.app (s.down.obj j)))) i

/-- 旧頂点の成分は、元の同じ自然変換成分の cycle と異種等号で一致する。 -/
lemma strictBarNativeSimplexApp_castSucc_heq {F G : J ⥤ ModuleCategory A PUnit.{1}}
    (η : F ⟶ G) {n : ℕ} (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (i : Fin (n + 1)) :
    HEq (strictBarNativeSimplexApp A J η s i.castSucc)
      (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (η.app (s.down.obj i))) := by
  simp only [strictBarNativeSimplexApp, Fin.lastCases_castSucc]
  exact strictBarCycleAlongEq_heq (A := A) (E := RightModule A PUnit.{1}) _ _ _

/-- apex の成分は、同じ正規化 bar の射の cycle と異種等号で一致する。 -/
lemma strictBarNativeSimplexApp_last_heq {F G : J ⥤ ModuleCategory A PUnit.{1}}
    (η : F ⟶ G) {n : ℕ} (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    HEq (strictBarNativeSimplexApp A J η s (Fin.last (n + 1)))
      (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (strictBarNormalizedMap A J η)) := by
  simp only [strictBarNativeSimplexApp, Fin.lastCases_last]
  exact strictBarCycleAlongEq_heq (A := A) (E := RightModule A PUnit.{1}) _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
