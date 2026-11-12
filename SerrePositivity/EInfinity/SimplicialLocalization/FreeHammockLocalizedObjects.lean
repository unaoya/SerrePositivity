module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockObjects
public import SerrePositivity.EInfinity.Hammock.FixedObjectLocalizationValue

/-!
# 自由 hammock と既存 DK Hom の対象表示の照合

概要：局所化前の自由対象の像が、既存 DK Hom の固定対象に一致することを証明する。
方針：両側の標準生成対象による表示を照合する。
規約：対象の一致と全単体作用素への自然性は証明し、追加の入力にしない。
使われ方：自由 hammock の局所化 Hom への評価への実際のデータの代入。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Opposite
open scoped Simplicial

lemma freeResolutionObject_localized (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ)
    (X : C.category) :
    ((freeResolution C).obj n).weakEquivalences.Q.obj (freeResolutionObject C n X) =
      localizedFreeResolutionObject C n X := by
  change ((freeResolution C).obj (op ⦋n.unop.len⦌)).weakEquivalences.Q.obj
    (freeResolutionObject C (op ⦋n.unop.len⦌) X) =
      localizedFreeResolutionObject C (op ⦋n.unop.len⦌) X
  rw [freeResolutionObject_generator, localizedFreeResolutionObject_generator]
  rfl

def freeHammockLocalizationObjects (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    Hammock.FixedObjectDiagram.LocalizationObjects (freeResolution C) C.category where
  original := freeResolutionObject C
  original_naturality := fun θ X => freeResolutionObject_naturality C θ X
  localized := localizedFreeResolutionObject C
  localized_naturality := fun θ X => localizedFreeResolutionObject_naturality C θ X
  image_eq := freeResolutionObject_localized C

end SerrePositivity.EInfinity.SimplicialLocalization
