module

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorAction
public import SerrePositivity.KST.Spectra.SuspensionLoop

/-!
概要：内部 Hom の源交換と suspension の写像空間への作用の整合性。
方針：反復評価で tensor strength と源交換の因子の順序を照合する。
規約：点つき閉対称モノイダル構造の厳密な等式。使われ方：整合写像空間と cotensor の交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.InternalHomExchange

@[reassoc]
lemma suspension_strength (X A Y : PointedSimplicialSet.{u}) :
    suspensionHom X ((ihom A).obj Y) ≫
        (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X)).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map PointedSimplicialSet.circle.{u} A Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y)).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso X A Y).hom ≫ (ihom A).map (suspensionHom X Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorHom_strength PointedSimplicialSet.circle.{u} X A Y

end SerrePositivity.KST.Spectra.InternalHomExchange
