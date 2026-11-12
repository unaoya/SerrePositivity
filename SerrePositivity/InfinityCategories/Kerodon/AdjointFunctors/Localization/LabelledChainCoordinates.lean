module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ChainCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChain
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElementsBaseChange
public import Mathlib.Logic.Equiv.Prod
/-!
# 元の両端ラベル付き射列の隣接 Hom 因子

概要：元の射列を頂点列ごとの隣接 Hom の依存積と元の両端ラベルへ回収する。
方針：両端ラベルによる元の全射列の復元と隣接 Hom 座標の全単射を合成する。
規約：底と両係数を同時に送る元の比較に厳密に自然。
使われ方：DK10.6(ii)の固定射列長の部分対角の因子分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates
open CategoryTheory Opposite
variable {C : Type u} [Category.{u} C] (A : Cᵒᵖ ⥤ Type u) (B : C ⥤ Type u) (k : ℕ)
abbrev Fiber (x : Fin (k + 1) → C) :=
  (∀ i : Fin k, x i.castSucc ⟶ x i.succ) × A.obj (op (x (Fin.last k))) × B.obj (x 0)

def equivalence : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element A B) k ≃
    Σ x : Fin (k + 1) → C, Fiber A B k x :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChain.chainEquiv A B k).trans
    ((Equiv.sigmaCongr (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ChainCoordinates.equivalence k) (fun _ => Equiv.refl _)).trans
      ((Equiv.sigmaAssoc (fun x _ => A.obj (op (x (Fin.last k))) × B.obj (x 0))).trans
        (Equiv.sigmaCongrRight (fun _ => Equiv.sigmaEquivProd _ _))))

lemma equivalence_apply (e : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element A B) k) :
    equivalence A B k e =
      ⟨fun i => (e.obj i).base, (fun i => (e.map (homOfLE (Fin.castSucc_le_succ i))).base),
        (e.obj (Fin.last k)).left, (e.obj 0).right⟩ := rfl

variable {A B k} {D : Type u} [Category.{u} D] (H : C ⥤ D)
  {A' : Dᵒᵖ ⥤ Type u} {B' : D ⥤ Type u}
  (α : A ⟶ H.op ⋙ A') (β : B ⟶ H ⋙ B')

def map (e : Σ x : Fin (k + 1) → C, Fiber A B k x) :
    Σ x : Fin (k + 1) → D, Fiber A' B' k x :=
  ⟨H.obj ∘ e.1, (fun i => H.map (e.2.1 i)),
    α.app (op (e.1 (Fin.last k))) e.2.2.1, β.app (e.1 0) e.2.2.2⟩

lemma equivalence_map (e : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element A B) k) :
    equivalence A' B' k
      (e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map α β ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pre H A' B') =
        map H α β (equivalence A B k e) := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates
