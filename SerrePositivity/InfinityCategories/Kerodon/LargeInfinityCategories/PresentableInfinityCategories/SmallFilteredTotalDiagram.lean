module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFilteredTotalCofinal
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPartialColimits

/-!
概要：部分添字の全空間上の元の図式から、指定した各部分図式を厳密に回収する。
方針：同じ部分添字 A の fiber を全空間へ含め、値射影との合成を比較する。
規約：元の標的図式と全単体を保持。部分余極限の coherent な選択はまだ結論しない。
使われ方：部分添字への射影に沿う左 Kan 拡張で、各値を部分余極限と同定する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] {I : Type u} [PartialOrder I]

/-- 同じ部分添字 A に属する対象を、全空間へ含める関手。 -/
def smallFilteredTotalFiber (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) : A.val ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFilteredTotal κ μ I where
  obj x := ⟨⟨A, x.val⟩, x.property⟩
  map f := homOfLE ⟨le_refl A, leOfHom f⟩

/-- 指定 fiber の全値射影は、元の部分 poset の包含と厳密に等しい。 -/
lemma smallFilteredTotalFiber_value (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) :
    smallFilteredTotalFiber A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalValue = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion A.val :=
  CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- 同じ fiber の部分添字射影は、厳密に指定した A に固定されている。 -/
lemma smallFilteredTotalFiber_piece (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) :
    smallFilteredTotalFiber A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalPiece = (Functor.const A.val).obj A :=
  CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- 全空間の値図式の指定 fiber への制限は、元の同じ部分図式そのもの。 -/
lemma smallFilteredTotalDiagram_restrict_fiber {C : SSet.{u + 1}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ C)
    (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (smallFilteredTotalFiber A)) ≫
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalValue) ≫ D) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredPartialDiagram D A := by
  have he : nerveMap (smallFilteredTotalFiber A) ≫ nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredTotalValue =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion A.val) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredPartialDiagram]
  rw [← Category.assoc, ← Functor.map_comp, he]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
