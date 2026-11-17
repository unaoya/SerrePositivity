module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.HomAugmentation
public import Mathlib.Data.Quot

/-!
# 単体的局所化の連結成分の圏

概要：Dwyer–Kan の実際の Hom の π₀ を射とする圏を構成する。
方針：辺の合成で元の合成を二重商へ降ろし、全法則を元の零単体で照合する。
規約：元の Hom の全単体は保持し、π₀ の圏は比較のために別に構成する。
使われ方：普通の局所化と DK Hom の π₀ の同値の証明。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization

open _root_.CategoryTheory _root_.Opposite
open scoped _root_.Simplicial

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

/-- 概要：同じ DK Hom の二本の辺を元の合成で合成する（Dwyer–Kan）。
方針：一次単体を合成し、面の合成保存で両端を照合する。
規約：元の局所化の合成順序を保持する。
使われ方：連結成分上の合成の代表独立性。 -/
def localizationHomEdgeComposition {X Y Z : C.category}
    {f f' : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y) _⦋0⦌} {g g' : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C Y Z) _⦋0⦌}
    (e : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y).Edge f f') (e' : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C Y Z).Edge g g') :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Z).Edge (f ≫ g) (f' ≫ g') :=
  .mk (e.edge ≫ e'.edge)
    (by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolution C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject C)
        (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject_naturality C θ X)
        (SimplexCategory.δ 1).op (e.edge ≫ e'.edge) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map_composition]
      exact congrArg₂ (fun a b => a ≫ b) e.src_eq e'.src_eq)
    (by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolution C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject C)
        (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject_naturality C θ X)
        (SimplexCategory.δ 0).op (e.edge ≫ e'.edge) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map_composition]
      exact congrArg₂ (fun a b => a ≫ b) e.tgt_eq e'.tgt_eq)

unseal SSet.π₀ in
/-- 概要：同じ DK Hom の合成を連結成分へ降ろす（Dwyer–Kan）。
方針：元の辺の合成を使い、両方の商関係に関して降下させる。
規約：元の零単体の合成を保持する。
使われ方：連結成分の圏の合成。 -/
def localizationComponentsComposition {X Y Z : C.category} :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y) → SSet.π₀ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C Y Z) →
      SSet.π₀ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Z) :=
  Quot.lift₂ (fun f g => SSet.π₀.mk (f ≫ g))
    (by rintro f g g' ⟨e⟩; exact SSet.π₀.sound (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomEdgeComposition C (.id f) e))
    (by rintro f f' g ⟨e⟩; exact SSet.π₀.sound (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomEdgeComposition C e (.id g)))

/-- 概要：DK の連結成分の圏の対象の型（Dwyer–Kan）。
方針：元の対象の別名を使い、元の相対圏の圏構造と区別する。
規約：対象の同型類への商は取らない。
使われ方：π₀ の比較圏。 -/
def LocalizationComponents : Type u := C.category

/-- 概要：DK の Hom の π₀ と元の合成は圏をなす（Dwyer–Kan）。
方針：商の全射性で代表へ戻して元の単位則・結合則を使う。
規約：元の Hom を離散化せず別の比較圏を構成する。
使われ方：普通の局所化への比較関手。 -/
instance localizationComponentsCategory : Category (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationComponents C) where
  Hom X Y := SSet.π₀ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y)
  id X := SSet.π₀.mk (𝟙 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject C (op ⦋0⦌) X))
  comp f g := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsComposition C f g
  id_comp f := by
    induction f using SSet.π₀.rec with
    | mk f => exact congrArg SSet.π₀.mk (Category.id_comp f)
  comp_id f := by
    induction f using SSet.π₀.rec with
    | mk f => exact congrArg SSet.π₀.mk (Category.comp_id f)
  assoc f g h := by
    induction f using SSet.π₀.rec with | mk f => ?_
    induction g using SSet.π₀.rec with | mk g => ?_
    induction h using SSet.π₀.rec with
    | mk h => exact congrArg SSet.π₀.mk (Category.assoc f g h)

/-- 概要：元の augmentation は連結成分の圏から普通の局所化への関手（Dwyer–Kan）。
方針：π₀ に降ろした同じ比較と全次数の単位・合成保存を使う。
規約：元の対象の局所化像と元の比較射を保持する。
使われ方：DK Hom の π₀ と普通の局所化 Hom の同値の順写像。 -/
def localizationComponentsAugmentation : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationComponents C ⥤ C.weakEquivalences.Localization
    where
  obj X := C.weakEquivalences.Q.obj X
  map := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomPiZeroToHom C _ _
  map_id X := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation_identity C X (op ⦋0⦌)
  map_comp f g := by
    induction f using SSet.π₀.rec with | mk f => ?_
    induction g using SSet.π₀.rec with
    | mk g => exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation_composition C (op ⦋0⦌) f g

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
