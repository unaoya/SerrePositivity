module

public meta import SerrePositivity.Util.Citation
public import Mathlib.CategoryTheory.Sites.LeftExact
public import SerrePositivity.InfinityCategories.Sheaves.SheafificationReflection
public import SerrePositivity.InfinityCategories.Sheaves.SpacePresheafYoneda
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.LargeNerveNatTransComponent

/-!
概要：通常の層化の指定単位が定める空間値前層の円柱。
方針：集合値の全自然変換の nerve 円柱を、指定された離散前層の埋め込みで後合成する。
  文献対応：HTT 6.2.2.7・5.5.4.15 の離散係数の場合。
使われ方：層化の比較射とその各成分を同じ円柱から読む。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves

/-- 通常の層化単位の全円柱を元の離散前層の埋め込みに沿って送る。 -/
@[cite HTT "6.2.2.7" (partial := special) "小さい通常の site 上の離散係数の層化単位。"]
def ordinarySheafificationUnit_postHomotopy :
    ∀ {C : Type u} [SmallCategory C]
      (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u}),
    let S := presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)
    let I := (discretePresheafInclusion C).val
    SSet.Homotopy I (nerveMap S ≫ I) := by
  intro C hC J hJ S I
  let H := largeNerveNatTransHomotopy (sheafificationAdjunction J (Type u)).unit
  have hid : nerveMap (𝟭 (Cᵒᵖ ⥤ Type u)) = 𝟙 _ :=
    nerveFunctor.map_id (Cat.of (Cᵒᵖ ⥤ Type u))
  refine ⟨H.h ≫ I, ?_, ?_, ?_⟩
  · change SSet.ι₀ ≫ (H.h ≫ I) = I
    rw [← Category.assoc, H.h₀, hid, Category.id_comp]
  · change SSet.ι₁ ≫ (H.h ≫ I) = nerveMap S ≫ I
    rw [← Category.assoc, H.h₁]
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories.Sheaves
