module

public import SerrePositivity.KST.Spectra.MappingKanSequence
public import SerrePositivity.KST.Spectra.KanSequenceCategory

/-!
概要：固定した点つき源からの内部 Hom 列を厳密な関手へまとめる。
方針：各段の内部 Hom の関手法則と、源制限の自然性を使う。
規約：構造射の単射性や Ω 条件は不要。使われ方：homotopy end の写像空間交換。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.KanSequence

/-- 任意の Kan 列を内部 Hom 列へ送る厳密な関手。 -/
def mappingFunctor (A : PointedSimplicialSet.{u}) : KanSequence.{u} ⥤ KanSequence.{u} where
  obj := mapping A
  map := mappingPost A
  map_id X := by
    apply Hom.ext_app
    intro n
    exact CategoryTheory.Functor.map_id (ihom A) _
  map_comp f g := by
    apply Hom.ext_app
    intro n
    exact CategoryTheory.Functor.map_comp (ihom A) _ _

/-- 内部 Hom の源の制限は、Kan 列全体について厳密に自然。 -/
def mappingPreTransformation {A B : PointedSimplicialSet.{u}} (i : A ⟶ B) :
    mappingFunctor B ⟶ mappingFunctor A where
  app := mappingPre i
  naturality X Y f := by
    apply Hom.ext_app
    intro n
    change (ihom B).map (f.app n) ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (Y.level n).space =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (X.level n).space ≫ (ihom A).map (f.app n)
    simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact (MonoidalClosed.pre i).naturality (f.app n)

end SerrePositivity.KST.Spectra.KanSequence
