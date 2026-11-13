module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomReindex
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# 最後の最大座標から元の始点の Under 圏へ

概要：最後の頂点へ至る path を始点から最大座標への矢へ送る。
方針：有限順序の Under 圏で関手を作り、最大座標の合成則と添字変換を使う。
規約：元の path・全包含・全単体作用素を保持する。
使われ方：native roof prism の Hom から prefix 円柱への座標。
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

abbrev LastPath (n : ℕ) (i : Fin (n + 1)) :=
  Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up (Fin.last (n + 1)))

def underFin {n : ℕ} (i : Fin (n + 1)) : LastPath.{u} n i ⥤ Under i where
  obj P := Under.mk (homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.le_pathLastMaximum P i P.left))
  map f := Under.homMk (homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_mono f.1.1.1)) (Subsingleton.elim _ _)

def indexFunctor {n : ℕ} (i : Fin (n + 1)) : LastPath.{u} n i ⥤ Fin (n + 1) where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum
  map f := homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_mono f.1.1.1)

lemma underFin_forget {n : ℕ} (i : Fin (n + 1)) :
    underFin.{u} i ⋙ Under.forget i = indexFunctor i := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intros
  apply Subsingleton.elim

lemma underFin_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastReindexFunctor.{u} α i ⋙ underFin (α.toOrderHom i) =
      underFin i ⋙ Under.post α.toOrderHom.monotone.functor := by
  refine CategoryTheory.Functor.ext
    (fun P => StructuredArrow.obj_ext _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_reindex α P)
      (Subsingleton.elim _ _)) ?_
  intros
  apply Under.UnderMorphism.ext
  apply Subsingleton.elim

lemma underFin_comp {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    compFunctor (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ ⋙ underFin i =
    CategoryTheory.Prod.snd _ _ ⋙ underFin j ⋙ Under.map (homOfLE hij) := by
  refine CategoryTheory.Functor.ext
    (fun P => StructuredArrow.obj_ext _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_comp P.1 P.2)
      (Subsingleton.elim _ _)) ?_
  intros
  apply Under.UnderMorphism.ext
  apply Subsingleton.elim

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
