module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

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
end SerrePositivity.KST.LocalizingInvariants.VerdierDiagram
namespace SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.VerdierDiagram
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.LocalizingInvariants.VerdierDiagram

instance instCategory : Category _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.{u} where
  Hom D E := FunctorHom D.square E.square
  id D := 𝟙 (HomotopyCategory.mk (functorVertex D.square))
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

end SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.VerdierDiagram

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.VerdierDiagram.instCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.instCategory := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.VerdierDiagram.instCategory

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.instCategory._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.VerdierDiagram.instCategory._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.instCategory._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.VerdierDiagram.instCategory._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierDiagram.instCategory._proof_3 := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.VerdierDiagram.instCategory._proof_3
