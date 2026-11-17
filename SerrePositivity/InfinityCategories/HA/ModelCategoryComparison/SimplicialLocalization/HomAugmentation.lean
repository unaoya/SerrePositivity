module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.EnrichedMap
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# 単体的局所化の Hom から普通の局所化 Hom への比較

概要：Dwyer–Kan の全解像の augmentation を固定 Hom の比較へ束ねる。
方針：同じ対象表示と augmentation を固定 Hom の係数自然性へ代入する。
規約：比較先だけを定値にし、元の Hom の全単体を保持する。
使われ方：DK と元の Map^h の比較の零次の正規化。
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

/-- 概要：全解像の augmentation は元の対象の局所化像を回収する（Dwyer–Kan）。
方針：同じ augmentation の対象同値の順逆則を使う。
規約：元の対象表示を保持する。
使われ方：固定 Hom の augmentation の対象整合性。 -/
lemma localizedFreeResolutionAugmentation_object (n : SimplexCategoryᵒᵖ) (X : C.category) :
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionAugmentation C).app n).toFunctor.obj
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject C n X) = C.weakEquivalences.Q.obj X :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObjectEquiv C n).apply_symm_apply _

/-- 概要：元の普通の局所化の両対象の Hom の定値単体集合（Dwyer–Kan）。
方針：元の局所化 Hom を全次数で一定にする。
規約：局所化前の単体的 Hom は変更しない。
使われ方：augmentation の比較先。 -/
abbrev localizationHomConstant (X Y : C.category) : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (C.weakEquivalences.Q.obj X ⟶ C.weakEquivalences.Q.obj Y)

/-- 概要：元の全 augmentation は固定 Hom の単体写像を与える（Dwyer–Kan）。
方針：同じ augmentation と対象表示の順逆則を係数自然変換へ代入する。
規約：成分は元の augmentation による Hom 作用。
使われ方：π₀ と普通の局所化 Hom の比較。 -/
def localizationHomAugmentation (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomConstant C X Y := by
  let η := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolution C)
    ((Functor.const SimplexCategoryᵒᵖ).obj (Cat.of C.weakEquivalences.Localization))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject C) (fun _ X => C.weakEquivalences.Q.obj X)
    (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject_naturality C θ X) (fun _ _ => rfl)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionAugmentation C) id
    (fun n X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionAugmentation_object C n X) X Y
  refine { app := η.app, naturality := ?_ }
  intro n m θ
  apply ConcreteCategory.hom_ext
  intro f
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.functor, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map]

/-- 概要：固定 Hom の augmentation は元の恒等射を保つ（Dwyer–Kan）。
方針：元の成分関手の恒等則と対象移送の相殺を使う。
規約：全次数の同じ恒等射。
使われ方：π₀ での比較関手の単位。 -/
lemma localizationHomAugmentation_identity (X : C.category) (n : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation C X X).app n (𝟙 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject C n X)) =
      𝟙 (C.weakEquivalences.Q.obj X) := by
  simp [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientMap]

/-- 概要：固定 Hom の augmentation は元の射の合成を保つ（Dwyer–Kan）。
方針：元の成分関手の合成則と中間対象の移送の相殺を使う。
規約：全次数の同じ合成。
使われ方：π₀ での比較関手の合成。 -/
lemma localizationHomAugmentation_composition {X Y Z : C.category}
    (n : SimplexCategoryᵒᵖ) (f : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y).obj n)
    (g : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C Y Z).obj n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation C X Z).app n (f ≫ g) =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation C X Y).app n f ≫
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation C Y Z).app n g := by
  simp [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientMap, Category.assoc]

/-- 概要：同じ augmentation の比較は単体的 Hom の辺の両端で等しい（Dwyer–Kan）。
方針：辺を定値の比較先へ送り、両端の顔の等式を合成する。
規約：元の辺と全 augmentation を保持する。
使われ方：π₀ への比較の降下。 -/
lemma localizationHomAugmentation_edge {X Y : C.category}
    {f g : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y) _⦋0⦌} (e : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y).Edge f g) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation C X Y).app (op ⦋0⦌) f =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation C X Y).app (op ⦋0⦌) g := by
  have h := e.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation C X Y)
  exact h.src_eq.symm.trans h.tgt_eq

/-- 概要：単体的局所化 Hom の π₀ から普通の局所化 Hom への同じ比較（Dwyer–Kan）。
方針：元の augmentation の比較を辺の両端の等式で商へ降ろす。
規約：現段階では写像のみ。同値性は後続で証明する。
使われ方：元の Map^h の π₀ 同定との照合。 -/
def localizationHomPiZeroToHom (X Y : C.category) :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y) →
      (C.weakEquivalences.Q.obj X ⟶ C.weakEquivalences.Q.obj Y) :=
  SSet.π₀.lift ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation C X Y).app (op ⦋0⦌))
    (fun _ _ e => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation_edge C e)

/-- 概要：零単体の類の比較は元の augmentation の Hom 作用（Dwyer–Kan）。
方針：同じ π₀ の商写像の定義を評価する。
規約：元の零単体を保持する。
使われ方：DK と Map^h の比較の射の正規化。 -/
lemma localizationHomPiZeroToHom_mk {X Y : C.category} (f : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomPiZeroToHom C X Y (SSet.π₀.mk f) =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation C X Y).app (op ⦋0⦌) f := rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
