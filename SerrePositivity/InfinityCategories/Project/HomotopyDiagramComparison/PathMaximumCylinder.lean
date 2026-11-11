module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PathMaximumDiagram

/-!
# path の最大座標による元の Under 円柱への全座標

概要：最大座標から Under パラメータと同じ時間を同時に取り出す。
方針：元の最大座標の nerve 写像と全 Under 関手を組にする。
規約：全パラメータ・path 合成・面と退化を保持する。
使われ方：native roof prism の最後の頂点への Hom の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open CategoryTheory SimplicialThickening SSet MonoidalCategory CartesianMonoidalCategory
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {I : Type u} [Category.{u} I]

lemma underFunctor_nerve_forget {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (i : Fin (n + 1)) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.underFunctor Γ i) ≫ nerveMap (Under.forget (Γ.obj i)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm Γ := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro P
  have hi : (stdSimplex.objEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i).app d P)).toOrderHom.monotone.functor =
      P ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.indexFunctor i := by
    refine CategoryTheory.Functor.ext (fun k => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap_apply i P k) ?_
    intros
    apply Subsingleton.elim
  change P ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.underFunctor Γ i ⋙ Under.forget (Γ.obj i) =
    (stdSimplex.objEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i).app d P)).toOrderHom.monotone.functor ⋙ Γ
  rw [hi, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.underFunctor_forget, CategoryTheory.Functor.assoc]

def coordinates {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) : nerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.LastPath.{u} n i) ⟶ nerve (Under (Γ.obj i)) ⊗ Δ[1] :=
  lift (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.underFunctor Γ i))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i ≫ stdSimplex.map (SimplexCategory.mkHom t))

lemma coordinates_reindex {m n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (t : Fin (n + 1) →o Fin 2) (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastReindexFunctor.{u} α i) ≫ coordinates Γ t (α.toOrderHom i) =
      coordinates (α.toOrderHom.monotone.functor ⋙ Γ) (t.comp α.toOrderHom) i := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro P
  apply Prod.ext
  · exact congrArg (fun F => P ⋙ F) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.underFunctor_reindex Γ α i)
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap_naturality α i) d) P
    exact congrArg ((stdSimplex.map (SimplexCategory.mkHom t)).app d) h

lemma coordinates_comp {n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hij : i ≤ j) :
    eComp SSet (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ ≫ coordinates Γ t i =
    snd _ _ ≫ coordinates Γ t j ≫ (nerveMap (Under.map (Γ.map (homOfLE hij))) ▷ Δ[1]) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  rintro ⟨P, Q⟩
  apply Prod.ext
  · exact congrArg (fun F => (P.prod' Q) ⋙ F) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.underFunctor_comp Γ i j hij)
  · exact congrArg ((stdSimplex.map (SimplexCategory.mkHom t)).app d)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathLastMaximumMap_comp i j d P Q)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
