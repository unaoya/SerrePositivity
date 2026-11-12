module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctor
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.Over

/-!
概要：底上の図式を、標準単体上の局所図式の余極限として表示する。
方針：presheaf の密度表示を Over 圏へ持ち上げ、保存関手で写す。
規約：通常の単体集合の余極限であり、Cat_∞ の余極限の主張ではない。
使われ方：fiber ごとの関手の族を、元の pullback 上の大域的な図式へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams

/-- 概要：底への射を持つ単体集合の全単体を底上の図式にする。
方針：各単体の Yoneda 射を底の構造射に合成して Over へ持ち上げる。
規約：退化単体も含む全単体を添字にする。
使われ方：局所図式を互換な族として貼り合わせる添字圏。 -/
def simplexDiagram {A B : SSet.{u}} (a : A ⟶ B) : A.Elementsᵒᵖ ⥤ Over B :=
  Over.lift (Presheaf.functorToRepresentables A)
    ((Presheaf.coconeOfRepresentable A).ι ≫ (Functor.const A.Elementsᵒᵖ).map a)

/-- 概要：各標準単体から元の底上の図式への標準 cocone。
方針：密度表示の Yoneda 射を底上の射とする。
規約：頂点は元の構造射 a。
使われ方：局所の関手データの大域的な降下。 -/
def simplexCocone {A B : SSet.{u}} (a : A ⟶ B) : Cocone (simplexDiagram a) where
  pt := Over.mk a
  ι :=
    { app j := Over.homMk ((Presheaf.coconeOfRepresentable A).ι.app j) rfl
      naturality j k f := by
        apply Over.OverMorphism.ext
        exact (Presheaf.coconeOfRepresentable A).w f }

/-- 概要：元の底上の図式はその全単体の余極限。
方針：Over の忘却関手で密度表示の余極限性を反映する。
規約：通常の圏 Over B の余極限。
使われ方：fiber ごとの関手の逆向きの普遍性。 -/
def simplexCocone_isColimit {A B : SSet.{u}} (a : A ⟶ B) :
    IsColimit (simplexCocone a) := by
  apply isColimitOfReflects (Over.forget B)
  exact Presheaf.colimitOfRepresentable A

/-- 概要：余極限を保つ局所形の関手で写しても全単体の余極限表示が得られる。
方針：通常の関手の余極限保存を使う。
規約：保存性は明示的な仮定。pullback 関手では既存の保存性を使える。
使われ方：局所形が変動する互換な射の族から一つの大域図式を作る。 -/
def simplexCocone_map_isColimit {A B : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (a : A ⟶ B) [PreservesColimitsOfShape A.Elementsᵒᵖ F] :
    IsColimit (F.mapCocone (simplexCocone a)) :=
  isColimitOfPreserves F (simplexCocone_isColimit a)

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams
