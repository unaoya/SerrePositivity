module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomCorrespondence
public import SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity
public import SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagrams

/-!
概要：抽象 Verdier 列の四角形提示と、全関手図式の比較からなる圏。
方針：関手 ∞ 圏のホモトピー圏から恒等・合成を引き戻す。
規約：元の包含・商・零角を含む提示を保持。使われ方：局所化不変量で写す pro Verdier 図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.VerdierDiagram

instance : Category VerdierDiagram.{u} where
  Hom D E := FunctorHom D.square E.square
  id D := 𝟙 (HomotopyCategory.mk (functorVertex D.square))
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

end SerrePositivity.KST.LocalizingInvariants.VerdierDiagram
