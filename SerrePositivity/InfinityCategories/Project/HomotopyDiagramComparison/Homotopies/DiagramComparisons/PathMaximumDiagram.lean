module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.PathMaximumUnder

/-!
# 元の単体図式の最大座標への Under 関手

概要：有限順序の最大座標を元の任意の単体図式で送り、同じ始点からの矢を保つ。
方針：Under.post により元の図式を後合成する。
規約：全 path 合成と面・退化を全関手として保持する。
使われ方：native roof prism の元の Under パラメータ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open CategoryTheory SimplicialThickening SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {I : Type u} [Category.{u} I]

def underFunctor {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.LastPath.{u} n i ⥤ Under (Γ.obj i) := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.underFin i ⋙ Under.post Γ

lemma underFunctor_forget {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (i : Fin (n + 1)) :
    underFunctor Γ i ⋙ Under.forget (Γ.obj i) = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.indexFunctor i ⋙ Γ := rfl

lemma underPost_map {n : ℕ} (Γ : Fin (n + 1) ⥤ I) {i j : Fin (n + 1)} (hij : i ≤ j) :
    Under.map (homOfLE hij) ⋙ Under.post Γ =
      Under.post Γ ⋙ Under.map (Γ.map (homOfLE hij)) := by
  have ho (s : Under j) :
      (Under.map (homOfLE hij) ⋙ Under.post Γ).obj s =
        (Under.post Γ ⋙ Under.map (Γ.map (homOfLE hij))).obj s := by
    change Under.mk (Γ.map (homOfLE hij ≫ s.hom)) =
      Under.mk (Γ.map (homOfLE hij) ≫ Γ.map s.hom)
    rw [Γ.map_comp]
  refine CategoryTheory.Functor.ext ho ?_
  intro s t f
  apply Under.UnderMorphism.ext
  simp only [Under.comp_right, Under.eqToHom_right]
  change Γ.map f.right = eqToHom rfl ≫ Γ.map f.right ≫ eqToHom rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

lemma underFunctor_reindex {m n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastReindexFunctor.{u} α i ⋙ underFunctor Γ (α.toOrderHom i) =
      underFunctor (α.toOrderHom.monotone.functor ⋙ Γ) i := by
  dsimp only [underFunctor]
  rw [← CategoryTheory.Functor.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.underFin_reindex α i]
  rfl

lemma underFunctor_comp {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (i j : Fin (n + 1))
    (hij : i ≤ j) :
    compFunctor (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ ⋙ underFunctor Γ i =
    CategoryTheory.Prod.snd _ _ ⋙ underFunctor Γ j ⋙ Under.map (Γ.map (homOfLE hij)) := by
  dsimp only [underFunctor]
  rw [← CategoryTheory.Functor.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.underFin_comp i j hij]
  simp only [CategoryTheory.Functor.assoc]
  rw [underPost_map Γ hij]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
