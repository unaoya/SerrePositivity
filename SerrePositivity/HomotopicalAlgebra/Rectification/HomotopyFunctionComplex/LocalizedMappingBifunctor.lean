module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.LocalizedResolutionHom

/-!
# 中断した任意モデル源への一般化：LocalizedMappingBifunctor

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Extending arbitrary-source mapping spaces to all target objects。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0109][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0109
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Extending arbitrary-source mapping spaces to all target objects

The fibrant inclusion followed by an ordinary localization is a localization.
Its universal property extends the Ho(SSet)-valued family in the target,
including every source natural transformation. No functorial replacement of
source objects or target objects is assumed. Strict SSet rectification is
still a separate requirement of F1.
-/

@[expose] public section
universe v u vS uS vC uC
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  {H : Type uS} [Category.{vS} H] (L : SSet.{v} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{v})]
  {HC : Type uC} [Category.{vC} HC] (Q : C ⥤ HC)
  [Q.IsLocalization (weakEquivalences C)]

lemma localizedResolutionHom_inverts_target (X : Cᵒᵖ) :
    (weakEquivalences (FibrantObject C)).IsInvertedBy
      ((localizedResolutionHom hcof L).obj X) := by
  intro Y Y' f hf
  exact localizedResolutionHom_map_target_isIso hcof L X f hf

/-- Extension in the target to any ordinary homotopy category of C. -/
abbrev localizedTargetHom (X : Cᵒᵖ) : HC ⥤ H :=
  Localization.lift ((localizedResolutionHom hcof L).obj X)
    (localizedResolutionHom_inverts_target hcof L X) (FibrantObject.ι ⋙ Q)

/-- Computation on fibrant targets, including the actual mapping space. -/
def localizedTargetHomComparison (X : Cᵒᵖ) :
    (FibrantObject.ι ⋙ Q) ⋙ localizedTargetHom hcof L Q X ≅
      (localizedResolutionHom hcof L).obj X :=
  Localization.fac _ (localizedResolutionHom_inverts_target hcof L X) (FibrantObject.ι ⋙ Q)

/-- The target extension respects all source maps and their composition. -/
def localizedHomotopyMapping : Cᵒᵖ ⥤ HC ⥤ H where
  obj X := localizedTargetHom hcof L Q X
  map f := Localization.liftNatTrans (FibrantObject.ι ⋙ Q)
    (weakEquivalences (FibrantObject C)) _ _ _ _ ((localizedResolutionHom hcof L).map f)
  map_id X := by
    rw [(localizedResolutionHom hcof L).map_id, Localization.liftNatTrans_id]
  map_comp f g := by
    rw [(localizedResolutionHom hcof L).map_comp, Localization.comp_liftNatTrans]

lemma localizedHomotopyMapping_inverts_source :
    (weakEquivalences C).op.IsInvertedBy (localizedHomotopyMapping hcof L Q) := by
  intro X X' f hf
  have : ∀ T, IsIso (((localizedResolutionHom hcof L).map f).app T) :=
    fun T => localizedResolutionHom_map_source_isIso hcof L f hf T
  have : IsIso ((localizedResolutionHom hcof L).map f) :=
    NatIso.isIso_of_isIso_app _
  let e := Localization.liftNatIso (FibrantObject.ι ⋙ Q)
    (weakEquivalences (FibrantObject C)) _ _
    (localizedTargetHom hcof L Q X) (localizedTargetHom hcof L Q X')
    (asIso ((localizedResolutionHom hcof L).map f))
  exact inferInstanceAs (IsIso e.hom)

/-- Both variables descend to ordinary Ho(C), while the output retains Ho(SSet). -/
abbrev homotopyCategoryMapping : HCᵒᵖ ⥤ HC ⥤ H :=
  Localization.lift (localizedHomotopyMapping hcof L Q)
    (localizedHomotopyMapping_inverts_source hcof L Q) Q.op

/-- The all-target bifunctor on C, obtained from the actual ordinary localization. -/
abbrev homotopyMapping : Cᵒᵖ ⥤ C ⥤ H :=
  localizedHomotopyMapping hcof L Q ⋙ (Functor.whiskeringLeft C HC H).obj Q

/-- The final all-target value at a fibrant object is the original resolution Hom. -/
def homotopyMappingFibrantIso (X : Cᵒᵖ) (Y : FibrantObject C) :
    ((homotopyMapping hcof L Q).obj X).obj Y.obj ≅
      L.obj ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (Reedy.cosimplicialResolution X.unop).obj).obj Y.obj) :=
  (localizedTargetHomComparison hcof L Q X).app Y

/-- Inverting a target weak equivalence uses Q, not a chosen fibrant replacement. -/
lemma homotopyMapping_map_target_isIso (X : Cᵒᵖ) {Y Y' : C}
    (f : Y ⟶ Y') (hf : weakEquivalences C f) :
    IsIso (((homotopyMapping hcof L Q).obj X).map f) := by
  have : IsIso (Q.map f) := Localization.inverts Q (weakEquivalences C) f hf
  exact inferInstanceAs (IsIso ((localizedTargetHom hcof L Q X).map (Q.map f)))

/-- Source weak equivalences induce isomorphisms on every target, after descent. -/
lemma homotopyMapping_map_source_isIso {X X' : Cᵒᵖ}
    (f : X ⟶ X') (hf : weakEquivalences C f.unop) (Y : C) :
    IsIso (((homotopyMapping hcof L Q).map f).app Y) := by
  have : ∀ T, IsIso (((localizedResolutionHom hcof L).map f).app T) :=
    fun T => localizedResolutionHom_map_source_isIso hcof L f hf T
  have : IsIso ((localizedResolutionHom hcof L).map f) :=
    NatIso.isIso_of_isIso_app _
  let e := Localization.liftNatIso (FibrantObject.ι ⋙ Q)
    (weakEquivalences (FibrantObject C)) _ _
    (localizedTargetHom hcof L Q X) (localizedTargetHom hcof L Q X')
    (asIso ((localizedResolutionHom hcof L).map f))
  exact inferInstanceAs (IsIso (e.hom.app (Q.obj Y)))

/-- Computation using any weak fibrant replacement, with no functorial choice. -/
def homotopyMappingReplacementIso (X : Cᵒᵖ) {Y R : C} [IsFibrant R]
    (i : Y ⟶ R) (hi : weakEquivalences C i) :
    ((homotopyMapping hcof L Q).obj X).obj Y ≅
      L.obj ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (Reedy.cosimplicialResolution X.unop).obj).obj R) := by
  have := homotopyMapping_map_target_isIso hcof L Q X i hi
  exact asIso (((homotopyMapping hcof L Q).obj X).map i) ≪≫
    homotopyMappingFibrantIso hcof L Q X (FibrantObject.mk R)

/-- Every value has a genuine Kan mapping-space representative, and its
components are the morphisms in the specified ordinary localization. -/
theorem homotopyMapping_has_representative (X : Cᵒᵖ) (Y : C) :
    ∃ K : SSet.{v}, SSet.KanComplex K ∧
      Nonempty (((homotopyMapping hcof L Q).obj X).obj Y ≅ L.obj K) ∧
      Nonempty (SSet.π₀ K ≃ (Q.obj X.unop ⟶ Q.obj Y)) := by
  let d := MorphismProperty.factorizationData
    (trivialCofibrations C) (fibrations C) (CategoryTheory.Limits.terminal.from Y)
  have : Fibration d.p := ⟨d.hp⟩
  have : IsFibrant d.Z :=
    (isFibrant_iff_of_isTerminal d.p CategoryTheory.Limits.terminalIsTerminal).mpr inferInstance
  let q := Reedy.cosimplicialResolution X.unop
  have : IsIso (Q.map d.i) := Localization.inverts Q (weakEquivalences C) _ d.hi.2
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj d.Z,
    cosimplicialHom_kanComplex _ q.cofibrant q.homotopicallyConstant d.Z,
    ⟨homotopyMappingReplacementIso hcof L Q X d.i d.hi.2⟩, ?_⟩
  exact ⟨(resolutionPiZeroLocalizationEquiv Q q d.Z).trans
    (Iso.homCongr (Iso.refl _) (asIso (Q.map d.i)).symm)⟩

end SerrePositivity.HomotopyFunctionComplex
