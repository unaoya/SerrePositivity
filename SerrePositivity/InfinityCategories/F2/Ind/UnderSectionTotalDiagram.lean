module

public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionStrictDiagram
public import SerrePositivity.InfinityCategories.F2.Ind.ParametrizedSectionsForget
public import SerrePositivity.InfinityCategories.F1.Transport.LeftStrictTransportWeightedNerve

/-!
概要：パラメータ付き under 切断の全空間は、元の添字上の strict transport へ自然に写る。
方針：パラメータを保つ制限と相対前合成が、同じ内部 Hom の射であることを使う。
規約：元の射影の left fibration 性をこの変換の構成には要求しない。
使われ方：添字全体の高次を同時に保つ scaffold 比較の係数変換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B E : SSet.{u}} (p : E ⟶ B ⊗ nerve I)

/-- 同じ under 切断の全空間を値とする通常の図式。 -/
def underSectionTotalDiagram : I ⥤ SSet.{u} where
  obj := underSectionFamily p
  map := underSectionFamilyMap p
  map_id := underSectionFamilyMap_id p
  map_comp := underSectionFamilyMap_comp p

/-- 同じ係数図式から元の添字上の strict transport への一つの自然変換。 -/
def underSectionTotalForget :
    underSectionTotalDiagram p ⟶ leftStrictTransportDiagram (p ≫ snd B (nerve I)) where
  app i := parametrizedSectionsForget p (nerveMap (Under.forget i))
  naturality {i j} f := by
    apply vertexFiber_hom_ext _ (functorVertex (nerveMap (Under.forget j)))
    change (underSectionFamilyMap p f ≫ parametrizedSectionsForget p _) ≫ _ =
      (parametrizedSectionsForget p _ ≫ relativeFunctorPre _ _ (nerveUnderMap f)) ≫ _
    rw [Category.assoc, parametrizedSectionsForget_ι, underSectionFamilyMap,
      parametrizedSectionsPre_map, Category.assoc]
    change _ = parametrizedSectionsForget p (nerveMap (Under.forget i)) ≫
      relativeFunctorPre _ _ (nerveUnderMap f) ≫
        vertexFiberι _ (functorVertex (nerveUnderMap f ≫ nerveMap (Under.forget i)))
    rw [relativeFunctorPre_ι, ← Category.assoc, parametrizedSectionsForget_ι]

end SerrePositivity.InfinityCategories.F2.Ind
