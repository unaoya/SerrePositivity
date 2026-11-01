module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.LabelledChainCoordinates
/-!
# 固定頂点表示における元のラベル付き射列

概要：元の全対象の表示同値から固定頂点列ごとの隣接 Hom と両ラベルへ回収する。
方針：同じ頂点列の添字だけを同値で戻し、元の射列を逆全単射で復元する。
規約：底と両係数の元の比較に、指定した対象表示の等式による移送を含め自然。
使われ方：DK10.6(ii)の固定頂点列の直積の和。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FixedVertexChainCoordinates
open CategoryTheory Opposite
variable {O C : Type u} [Category.{u} C] (p : O ≃ C)
  (A : Cᵒᵖ ⥤ Type u) (B : C ⥤ Type u) (k : ℕ)
abbrev Fiber (x : Fin (k + 1) → O) := LabelledChainCoordinates.Fiber A B k (p ∘ x)

def equivalence : ComposableArrows (TwoSidedElements.Element A B) k ≃
    Σ x : Fin (k + 1) → O, Fiber p A B k x :=
  (LabelledChainCoordinates.equivalence A B k).trans
    (Equiv.sigmaCongrLeft (Equiv.piCongrRight (fun _ => p))).symm

def decode (x : Fin (k + 1) → O) (v : Fiber p A B k x) :
    ComposableArrows (TwoSidedElements.Element A B) k :=
  (LabelledChainCoordinates.equivalence A B k).symm ⟨p ∘ x, v⟩

lemma equivalence_symm_apply (x : Fin (k + 1) → O) (v : Fiber p A B k x) :
    (equivalence p A B k).symm ⟨x, v⟩ = decode p A B k x v := rfl

variable {p A B k} {D : Type u} [Category.{u} D] (q : O ≃ D) (H : C ⥤ D)
  {A' : Dᵒᵖ ⥤ Type u} {B' : D ⥤ Type u}
  (α : A ⟶ H.op ⋙ A') (β : B ⟶ H ⋙ B') (hp : ∀ o, H.obj (p o) = q o)

def fiberMap (x : Fin (k + 1) → O) (v : Fiber p A B k x) : Fiber q A' B' k x :=
  cast (congrArg (LabelledChainCoordinates.Fiber A' B' k) (funext (fun i => hp (x i))))
    (LabelledChainCoordinates.map H α β ⟨p ∘ x, v⟩).2

private lemma sigma_mk_cast {I : Type u} {P : I → Type u} {x y : I}
    (h : x = y) (v : P x) : (⟨y,cast (congrArg P h) v⟩ : Sigma P) = ⟨x, v⟩ := by
  cases h
  rfl

lemma decode_naturality (x : Fin (k + 1) → O) (v : Fiber p A B k x) :
    decode p A B k x v ⋙ TwoSidedElements.map α β ⋙ TwoSidedElements.pre H A' B' =
      decode q A' B' k x (fiberMap q H α β hp x v) := by
  apply (LabelledChainCoordinates.equivalence A' B' k).injective
  rw [LabelledChainCoordinates.equivalence_map]
  change LabelledChainCoordinates.map H α β
    ((LabelledChainCoordinates.equivalence A B k)
      ((LabelledChainCoordinates.equivalence A B k).symm ⟨p ∘ x, v⟩)) =
    (LabelledChainCoordinates.equivalence A' B' k)
      ((LabelledChainCoordinates.equivalence A' B' k).symm
        ⟨q ∘ x,fiberMap q H α β hp x v⟩)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact (sigma_mk_cast (funext (fun i => hp (x i))) _).symm

end SerrePositivity.EInfinity.Hammock.FixedVertexChainCoordinates
