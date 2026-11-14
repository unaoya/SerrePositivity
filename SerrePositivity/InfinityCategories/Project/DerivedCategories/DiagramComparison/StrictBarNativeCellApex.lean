module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplexFunctorEvaluation

/-!
概要：元の native セルの全族が、同じ正規化 bar の apex 関手を持つことを示す。
方針：閉零圏の零セルの通常関手と、元の apex の閉零成分を照合する。
規約：apex を対象ごとに別々に選ばない。
使われ方：3b-3 R6、固定 apex を持つ slice での全族の貼り合わせ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- 元の閉零加群を同じ HA 零セルとして読む通常関手。 -/
def strictBarClosedVertexFunctor :
    ModuleCategory A PUnit.{1} ⥤ StrictSimplexCategory A (RightModule A PUnit.{1}) 0 where
  obj M := ⟨closedNerveSimplex (A := A) (D := RightModule A PUnit.{1})
    ((Functor.const (Fin 1)).obj M)⟩
  map f := strictClosedSimplexMap (A := A) (E := RightModule A PUnit.{1})
    ((Functor.const (Fin 1)).map f)
  map_id M := by
    apply StrictSimplexMap.ext
    intro i
    change closedHomEquiv A (RightModule A PUnit.{1}) M M (𝟙 M) = _
    exact closedHom_id (A := A) (D := RightModule A PUnit.{1}) M
  map_comp f g := by
    apply StrictSimplexMap.ext
    intro i
    apply Subtype.ext
    change (closedHomEquiv A (RightModule A PUnit.{1}) _ _ (f ≫ g)).val =
      compose A (closedHomEquiv A (RightModule A PUnit.{1}) _ _ g).val
        (closedHomEquiv A (RightModule A PUnit.{1}) _ _ f).val (zero_add 0)
    exact closedHom_comp (A := A) (D := RightModule A PUnit.{1}) f g

variable (J : Type) [SmallCategory J]

/-- 元の native セルの最後の零セルは、同じ正規化 bar の零セル。 -/
lemma strictBarNativeApexSimplex_eq (F : J ⥤ ModuleCategory A PUnit.{1}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    (strictBarNativeSimplex A J F s).pullback (lastVertex n).toOrderHom =
      ((strictBarClosedVertexFunctor A).obj ((strictBarNormalizedFunctor A J).obj F)).val := by
  apply Simplex.vertexEquiv.injective
  change (strictBarNativeSimplex A J F s).obj (Fin.last (n + 1)) = _
  exact dgCoherentBarNativeSimplex_last A PUnit.{1} (smallStrictBarDiagram A F)
    (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s

/-- 同じ apex 零セルへの制限は、元の正規化 bar 関手と全射で一致する。 -/
lemma strictBarNativeSimplexFunctor_apex {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    strictBarNativeSimplexFunctor A J s ⋙
        strictSimplexPullbackFunctor A (RightModule A PUnit.{1}) (lastVertex n).toOrderHom =
      strictBarNormalizedFunctor A J ⋙ strictBarClosedVertexFunctor A := by
  apply CategoryTheory.Functor.hext
  · intro F
    exact congrArg (fun t : Simplex A (RightModule A PUnit.{1}) 0 =>
        (⟨t⟩ : StrictSimplexCategory A (RightModule A PUnit.{1}) 0))
      (strictBarNativeApexSimplex_eq A J F s)
  · intro F G η
    apply StrictSimplexMap.hext
    · exact congrArg Simplex.toSimplexData (strictBarNativeApexSimplex_eq A J F s)
    · exact congrArg Simplex.toSimplexData (strictBarNativeApexSimplex_eq A J G s)
    · intro i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst i
      exact strictBarNativeSimplexApp_last_heq A J η s

/-- 同じ正規化 bar の apex の全パラメーター零セル評価。 -/
def strictBarApexCellEvaluation :
    nerve (J ⥤ ModuleCategory A PUnit.{1}) ⊗ (Δ[0] : SSet.{u + 1}) ⟶
      dgNerve A (RightModule A PUnit.{1}) :=
  strictSimplexFunctorEvaluation A (RightModule A PUnit.{1})
    (strictBarNormalizedFunctor A J ⋙ strictBarClosedVertexFunctor A)

/-- 元の全 native セルの apex の評価は、同じ全 apex 評価へ一致する。 -/
lemma strictBarNativeCellEvaluation_apex {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    (nerve (J ⥤ ModuleCategory A PUnit.{1}) ◁ SSet.stdSimplex.map (lastVertex n)) ≫
        strictBarNativeCellEvaluation A J s = strictBarApexCellEvaluation A J := by
  change _ ≫ strictSimplexFunctorEvaluation A (RightModule A PUnit.{1})
      (strictBarNativeSimplexFunctor A J s) = _
  have hp := strictSimplexFunctorEvaluation_pullback A (RightModule A PUnit.{1})
    (strictBarNativeSimplexFunctor A J s) (lastVertex n).toOrderHom
  change strictSimplexFunctorEvaluation A (RightModule A PUnit.{1})
      (strictBarNativeSimplexFunctor A J s ⋙
        strictSimplexPullbackFunctor A (RightModule A PUnit.{1})
          (lastVertex n).toOrderHom) = _ at hp
  exact hp.symm.trans (congrArg
    (strictSimplexFunctorEvaluation A (RightModule A PUnit.{1}))
    (strictBarNativeSimplexFunctor_apex A J s))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
