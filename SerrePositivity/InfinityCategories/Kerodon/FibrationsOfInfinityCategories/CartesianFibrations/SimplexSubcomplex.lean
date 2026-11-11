module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.StandardLocalization
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
概要：底の部分複体と単体圏の nerve の部分複体の厳密な比較。
方針：射列の最初の単体が部分複体に入れば、後続の全単体も入ることを使う。
規約：単射の像を頂点条件だけで近似せず、実際の nerve との同型を与える。
使われ方：標準単体の局所化を境界と一般の底へ貼り合わせる比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 部分複体に入る最初の単体から始まる射列は、その後も部分複体に入る。 -/
lemma transportSimplexChain_mem_of_first {B : SSet.{u}} (K : B.Subcomplex) {n : ℕ}
    (σ : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) n)
    (h : (σ.obj 0).objDown.val ∈ K.obj (σ.obj 0).objDown.obj) (i : Fin (n + 1)) :
    (σ.obj i).objDown.val ∈ K.obj (σ.obj i).objDown.obj := by
  have hi := K.map (σ.map (homOfLE (Fin.zero_le i))).down.hom h
  change B.map _ (σ.obj 0).objDown.val ∈ K.obj (σ.obj i).objDown.obj at hi
  rw [(σ.map (homOfLE (Fin.zero_le i))).down.map_val] at hi
  exact hi

/-- 最初の単体の所属で記述した、全単体の nerve の部分複体。 -/
def transportSimplexNerveSubcomplex {B : SSet.{u}} (K : B.Subcomplex) :
    (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)).Subcomplex where
  obj _ := {σ | (σ.obj 0).objDown.val ∈ K.obj (σ.obj 0).objDown.obj}
  map {d e} α := by
    intro σ h
    exact transportSimplexChain_mem_of_first K σ h (α.unop.toOrderHom 0)

/-- 部分複体への所属証明を射列の全対象に付け、実際の単体圏へ持ち上げる。 -/
def transportSimplexSubcomplexLiftChain {B : SSet.{u}} (K : B.Subcomplex) {n : ℕ}
    (σ : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) n)
    (h : (σ.obj 0).objDown.val ∈ K.obj (σ.obj 0).objDown.obj) :
    ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (K : SSet.{u})) n where
  obj i := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex
    ⟨(σ.obj i).objDown.val, transportSimplexChain_mem_of_first K σ h i⟩
  map {i j} f := ⟨{ hom := (σ.map f).down.hom
                    map_val := Subtype.ext (σ.map f).down.map_val }⟩
  map_id i := by
    apply ULift.ext
    apply CategoryTheory.Functor.Elements.Hom.ext
    exact congrArg (fun f ↦ f.down.hom) (σ.map_id i)
  map_comp f g := by
    apply ULift.ext
    apply CategoryTheory.Functor.Elements.Hom.ext
    exact congrArg (fun f ↦ f.down.hom) (σ.map_comp f g)

/-- 部分複体の単体圏の nerve は、最初の単体の所属による部分複体へ写る。 -/
def transportSimplexSubcomplexForward {B : SSet.{u}} (K : B.Subcomplex) :
    nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (K : SSet.{u})) ⟶
      (transportSimplexNerveSubcomplex K : SSet.{u}) where
  app _ := ↾fun σ ↦ ⟨σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor K.ι, (σ.obj 0).objDown.val.property⟩
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    rfl

/-- 所属条件で記述した部分複体から、元の部分複体の単体圏の nerve へ戻す。 -/
def transportSimplexSubcomplexBackward {B : SSet.{u}} (K : B.Subcomplex) :
    (transportSimplexNerveSubcomplex K : SSet.{u}) ⟶
      nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (K : SSet.{u})) where
  app _ := ↾fun σ ↦ transportSimplexSubcomplexLiftChain K σ.val σ.property
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro σ
    rfl

/-- 部分複体の単体圏の nerve と、最初の単体で記述した部分複体は厳密に同型。 -/
def transportSimplexSubcomplexIso {B : SSet.{u}} (K : B.Subcomplex) :
    nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (K : SSet.{u})) ≅
      (transportSimplexNerveSubcomplex K : SSet.{u}) where
  hom := transportSimplexSubcomplexForward K
  inv := transportSimplexSubcomplexBackward K
  hom_inv_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro σ
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    rfl

/-- 厳密な同型は実際の単体圏の nerve の包含と可換。 -/
lemma transportSimplexSubcomplexIso_ι {B : SSet.{u}} (K : B.Subcomplex) :
    (transportSimplexSubcomplexIso K).hom ≫ (transportSimplexNerveSubcomplex K).ι =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor K.ι) := rfl

/-- 底の部分複体の包含は、単体圏の nerve でも単射。 -/
instance transportSimplexSubcomplex_nerveMap_mono {B : SSet.{u}} (K : B.Subcomplex) :
    Mono (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor K.ι)) := by
  rw [← transportSimplexSubcomplexIso_ι]
  infer_instance

/-- 共通部分への制限は、単体圏の nerve の部分複体でも共通部分そのもの。 -/
lemma transportSimplexNerveSubcomplex_inf {B : SSet.{u}} (K L : B.Subcomplex) :
    transportSimplexNerveSubcomplex (K ⊓ L) =
      transportSimplexNerveSubcomplex K ⊓ transportSimplexNerveSubcomplex L := rfl

/-- 合併への制限は、単体圏の nerve の部分複体でも合併そのもの。 -/
lemma transportSimplexNerveSubcomplex_sup {B : SSet.{u}} (K L : B.Subcomplex) :
    transportSimplexNerveSubcomplex (K ⊔ L) =
      transportSimplexNerveSubcomplex K ⊔ transportSimplexNerveSubcomplex L := rfl

/-- 部分複体の包含関係は単体圏の nerve の部分複体の包含関係を保つ。 -/
lemma transportSimplexNerveSubcomplex_mono {B : SSet.{u}} :
    Monotone (transportSimplexNerveSubcomplex (B := B)) := by
  intro K L h d σ hσ
  exact h _ hσ

/-- 部分複体の厳密な同型は、部分複体間の実際の包含とも可換。 -/
lemma transportSimplexSubcomplexIso_naturality {B : SSet.{u}} {K L : B.Subcomplex}
    (h : K ≤ L) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (Subcomplex.homOfLE h)) ≫
        (transportSimplexSubcomplexIso L).hom =
      (transportSimplexSubcomplexIso K).hom ≫
        Subcomplex.homOfLE (transportSimplexNerveSubcomplex_mono h) := rfl

/-- 部分複体の共通部分と合併による貼り合わせは、実際の単体圏の nerve で pushout。 -/
lemma transportSimplexNerve_bicart_isPushout {B : SSet.{u}}
    {K₁ K₂ K₃ K₄ : B.Subcomplex} (h : Subcomplex.BicartSq K₁ K₂ K₃ K₄) :
    IsPushout
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (Subcomplex.homOfLE h.le₁₂)))
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (Subcomplex.homOfLE h.le₁₃)))
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (Subcomplex.homOfLE h.le₂₄)))
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (Subcomplex.homOfLE h.le₃₄))) := by
  have hs : Subcomplex.BicartSq (transportSimplexNerveSubcomplex K₁)
      (transportSimplexNerveSubcomplex K₂) (transportSimplexNerveSubcomplex K₃)
      (transportSimplexNerveSubcomplex K₄) := {
    sup_eq := by rw [← transportSimplexNerveSubcomplex_sup, h.sup_eq]
    inf_eq := by rw [← transportSimplexNerveSubcomplex_inf, h.inf_eq] }
  apply hs.isPushout.of_iso' (transportSimplexSubcomplexIso K₁)
    (transportSimplexSubcomplexIso K₂) (transportSimplexSubcomplexIso K₃)
    (transportSimplexSubcomplexIso K₄)
  all_goals rfl

/-- 部分複体の逆像は、単体圏の nerve の実際の逆像と一致する。 -/
lemma transportSimplexNerveSubcomplex_preimage {B D : SSet.{u}}
    (K : D.Subcomplex) (f : B ⟶ D) :
    transportSimplexNerveSubcomplex (K.preimage f) =
      (transportSimplexNerveSubcomplex K).preimage
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor f)) := rfl

/-- 全体の部分複体を取ると、単体圏の nerve 全体になる。 -/
lemma transportSimplexNerveSubcomplex_top (B : SSet.{u}) :
    transportSimplexNerveSubcomplex (⊤ : B.Subcomplex) = ⊤ := rfl

/-- 空の部分複体を取ると、単体圏の nerve も空になる。 -/
lemma transportSimplexNerveSubcomplex_bot (B : SSet.{u}) :
    transportSimplexNerveSubcomplex (⊥ : B.Subcomplex) = ⊥ := rfl

/-- 部分複体の単体圏の同定は、元の初頂点写像とも厳密に可換。 -/
lemma transportSimplexSubcomplexIso_firstVertex {B : SSet.{u}} (K : B.Subcomplex) :
    (transportSimplexSubcomplexIso K).hom ≫ (transportSimplexNerveSubcomplex K).ι ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap (K : SSet.{u}) ≫ K.ι := by
  rw [← Category.assoc, transportSimplexSubcomplexIso_ι,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_naturality]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
