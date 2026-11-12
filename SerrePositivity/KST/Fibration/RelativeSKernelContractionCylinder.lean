module
public import SerrePositivity.KST.Fibration.RelativeSKernelSimplicialIso
public import SerrePositivity.KST.Fibration.StableZeroSContraction

/-! # 元の相対 S 核を、全段に共通の自然変換で収縮する全単体的実円柱 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の全相対 S 核における、全ての面・退化と全時刻で整合する実円柱。 -/
def relativeSKernelContractionCylinder
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    relativeSimplicialSConstruction (i.hom ≫ q.hom) ⋙ tensorRight (Δ[1] : SSet.{u}) ⟶
      relativeSimplicialSConstruction (i.hom ≫ q.hom) :=
  CategoryTheory.Functor.whiskerRight (relativeSKernelSimplicialIso h).hom
    (tensorRight (Δ[1] : SSet.{u})) ≫
    stableZeroSContractionNatTrans A ≫ (relativeSKernelSimplicialIso h).inv

/-- 元の各段の円柱は、同じ包含と同じ逆同型を介した元の S_n 円柱の評価。 -/
theorem relativeSKernelContractionCylinder_app
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : SimplexCategoryᵒᵖ) :
    (relativeSKernelContractionCylinder h).app n =
      ((relativeSKernelTopIso h n.unop.len).hom ▷ (Δ[1] : SSet.{u})) ≫
        stableZeroSContractionAction A n.unop.len ≫ (relativeSKernelTopIso h n.unop.len).inv :=
  rfl

end SerrePositivity.KST.Fibration
