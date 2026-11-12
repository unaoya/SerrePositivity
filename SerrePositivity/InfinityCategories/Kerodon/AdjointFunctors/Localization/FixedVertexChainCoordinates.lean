module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates
/-!
# 固定頂点表示における元のラベル付き射列

概要：元の全対象の表示同値から固定頂点列ごとの隣接 Hom と両ラベルへ回収する。
方針：同じ頂点列の添字だけを同値で戻し、元の射列を逆全単射で復元する。
規約：底と両係数の元の比較に、指定した対象表示の等式による移送を含め自然。
使われ方：DK10.6(ii)の固定頂点列の直積の和。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates
open CategoryTheory Opposite
variable {O C : Type u} [Category.{u} C] (p : O ≃ C)
  (A : Cᵒᵖ ⥤ Type u) (B : C ⥤ Type u) (k : ℕ)
abbrev Fiber (x : Fin (k + 1) → O) := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates.Fiber A B k (p ∘ x)

def equivalence : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element A B) k ≃
    Σ x : Fin (k + 1) → O, Fiber p A B k x :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates.equivalence A B k).trans
    (Equiv.sigmaCongrLeft (Equiv.piCongrRight (fun _ => p))).symm

def decode (x : Fin (k + 1) → O) (v : Fiber p A B k x) :
    ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element A B) k :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates.equivalence A B k).symm ⟨p ∘ x, v⟩

lemma equivalence_symm_apply (x : Fin (k + 1) → O) (v : Fiber p A B k x) :
    (equivalence p A B k).symm ⟨x, v⟩ = decode p A B k x v := rfl

variable {p A B k} {D : Type u} [Category.{u} D] (q : O ≃ D) (H : C ⥤ D)
  {A' : Dᵒᵖ ⥤ Type u} {B' : D ⥤ Type u}
  (α : A ⟶ H.op ⋙ A') (β : B ⟶ H ⋙ B') (hp : ∀ o, H.obj (p o) = q o)

def fiberMap (x : Fin (k + 1) → O) (v : Fiber p A B k x) : Fiber q A' B' k x :=
  cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates.Fiber A' B' k) (funext (fun i => hp (x i))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates.map H α β ⟨p ∘ x, v⟩).2

private lemma sigma_mk_cast {I : Type u} {P : I → Type u} {x y : I}
    (h : x = y) (v : P x) : (⟨y,cast (congrArg P h) v⟩ : Sigma P) = ⟨x, v⟩ := by
  cases h
  rfl

lemma decode_naturality (x : Fin (k + 1) → O) (v : Fiber p A B k x) :
    decode p A B k x v ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map α β ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pre H A' B' =
      decode q A' B' k x (fiberMap q H α β hp x v) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates.equivalence A' B' k).injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates.equivalence_map]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates.map H α β
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates.equivalence A B k)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates.equivalence A B k).symm ⟨p ∘ x, v⟩)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates.equivalence A' B' k)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates.equivalence A' B' k).symm
        ⟨q ∘ x,fiberMap q H α β hp x v⟩)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact (sigma_mk_cast (funext (fun i => hp (x i))) _).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates
