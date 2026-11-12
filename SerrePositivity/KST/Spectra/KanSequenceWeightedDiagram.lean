module

public import SerrePositivity.KST.Spectra.KanSequenceMappingFunctor
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreeIntervalBoundary
public import SerrePositivity.KST.Spectra.PointedWeightedEnd

/-!
概要：点つき重みの内部 Hom 図式を一般の Kan 列の二変数図式に持ち上げる。
方針：源の制限を反変関手とし、係数の図式を前合成する。
規約：重みは任意、構造射の単射性は不要。使われ方：homotopy end の写像空間交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed Opposite
namespace SerrePositivity.KST.Spectra.KanSequence

/-- 内部 Hom 列の源に関する反変な厳密な関手。 -/
def mappingBifunctor : PointedSimplicialSet.{u}ᵒᵖ ⥤ (KanSequence.{u} ⥤ KanSequence.{u}) where
  obj A := mappingFunctor A.unop
  map f := mappingPreTransformation f.unop
  map_id A := by
    apply NatTrans.ext
    funext X
    apply Hom.ext_app
    intro n
    change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (𝟙 A.unop) (X.level n).space = 𝟙 _
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, MonoidalClosed.pre_id, NatTrans.id_app]
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext X
    apply Hom.ext_app
    intro n
    exact (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp g.unop f.unop (X.level n).space).symm

/-- Kan 列の重み付き end の二変数図式。 -/
def weightedDiagram {I : Type u} [SmallCategory I] (W : I ⥤ SSet.{u})
    (D : I ⥤ KanSequence.{u}) : Iᵒᵖ ⥤ I ⥤ KanSequence.{u} :=
  (W ⋙ PointedObject.adjoinFunctor).op ⋙ mappingBifunctor ⋙
    (Functor.whiskeringLeft I KanSequence.{u} KanSequence.{u}).obj D

end SerrePositivity.KST.Spectra.KanSequence
