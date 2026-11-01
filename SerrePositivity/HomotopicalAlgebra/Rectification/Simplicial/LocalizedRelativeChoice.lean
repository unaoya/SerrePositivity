module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceSpace
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanRestrictionLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction
public import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
# 中断した任意モデル源への一般化：LocalizedRelativeChoice

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Contractible actual extension spaces along a localized mono equivalence。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0449][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0449
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Contractible actual extension spaces along a localized mono equivalence

The target is only required to be Kan. Every parameter monomorphism
admits extension, retaining the whole prescribed boundary. No model
structure or contractibility of the target is assumed.
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.LocalizedRelativeChoice
variable {A B K : SSet.{w}} (i : A ⟶ B) [Mono i]
  (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

def restrictionSection : (ihom A).obj K ⟶ (ihom B).obj K :=
  (MonoRightLiftingContraction.exists_section ((pre i).app K)
    (KanRestrictionLifting.all_mono_rlp i hi hK)).choose

lemma restrictionSection_fac : restrictionSection i hi hK ≫ (pre i).app K = 𝟙 _ :=
  (MonoRightLiftingContraction.exists_section ((pre i).app K)
    (KanRestrictionLifting.all_mono_rlp i hi hK)).choose_spec

def extension (f : A ⟶ K) : B ⟶ K :=
  uncurry' (curry' f ≫ restrictionSection i hi hK)

lemma name_extension (f : A ⟶ K) :
    RelativeChoiceSpace.name (extension i hi hK f) =
      RelativeChoiceSpace.name f ≫ restrictionSection i hi hK := by
  rw [RelativeChoiceSpace.name, extension, curry'_uncurry']
  exact (Category.assoc _ _ _).symm

lemma extension_fac (f : A ⟶ K) : i ≫ extension i hi hK f = f := by
  apply curry'_injective
  apply (cancel_epi RelativeChoiceSpace.pointUnitIso.hom).mp
  change RelativeChoiceSpace.name (i ≫ extension i hi hK f) = RelativeChoiceSpace.name f
  rw [← RelativeChoiceSpace.name_precomp, name_extension, Category.assoc]
  have hs : restrictionSection i hi hK ≫ (internalHom.map i.op).app K = 𝟙 _ :=
    restrictionSection_fac i hi hK
  rw [hs, Category.comp_id]

include hi hK in
lemma parameter_extension (f : A ⟶ K) {U V : SSet.{w}} (j : U ⟶ V) [Mono j]
    (a : U ⟶ RelativeChoiceSpace.obj i f) :
    ∃ b : V ⟶ RelativeChoiceSpace.obj i f, j ≫ b = a := by
  have : HasLiftingProperty j ((internalHom.map i.op).app K) :=
    KanRestrictionLifting.all_mono_rlp i hi hK j inferInstance
  have : HasLiftingProperty j (RelativeChoiceSpace.projection i f) := inferInstance
  let sq : CommSq a j (RelativeChoiceSpace.projection i f)
      (SSet.stdSimplex.isTerminalObj₀.from V) :=
    ⟨SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

include hi hK in
lemma terminal_mono_rlp (f : A ⟶ K) :
    (MorphismProperty.monomorphisms SSet.{w}).rlp
      (terminal.from (RelativeChoiceSpace.obj i f)) := by
  intro U V j hj
  have : Mono j := hj
  refine ⟨fun {a b} _ => ?_⟩
  obtain ⟨l, hl⟩ := parameter_extension i hi hK f j a
  exact ⟨⟨{ l := l, fac_left := hl, fac_right := terminal.hom_ext _ _ }⟩⟩

include hi hK in
lemma boundary_rlp (f : A ⟶ K) : SSet.modelCategoryQuillen.I.rlp
    (terminal.from (RelativeChoiceSpace.obj i f)) := by
  rw [← SSet.rlp_monomorphisms]
  exact terminal_mono_rlp i hi hK f

include hi hK in
lemma kan (f : A ⟶ K) : SSet.modelCategoryQuillen.J.rlp
    (terminal.from (RelativeChoiceSpace.obj i f)) := by
  intro U V j hj
  exact terminal_mono_rlp i hi hK f j (SSet.modelCategoryQuillen.J_le_monomorphisms j hj)

include hi hK in
lemma interval (f : A ⟶ K)
    (s t : SSet.stdSimplex.obj (SimplexCategory.mk 0) ⟶ RelativeChoiceSpace.obj i f) :
    ∃ e : SSet.stdSimplex.obj (SimplexCategory.mk 1) ⟶ RelativeChoiceSpace.obj i f,
      SSet.stdSimplex.δ (1 : Fin 2) ≫ e = s ∧ SSet.stdSimplex.δ (0 : Fin 2) ≫ e = t := by
  let a := HomotopyFunctionComplex.BoundaryOne.isColimit.desc (BinaryCofan.mk s t)
  obtain ⟨e, he⟩ := parameter_extension i hi hK f (SSet.boundary 1).ι a
  refine ⟨e, ?_, ?_⟩
  · rw [← SSet.boundary.ι_ι (1 : Fin 2), Category.assoc, he]
    exact HomotopyFunctionComplex.BoundaryOne.isColimit.fac
      (BinaryCofan.mk s t) ⟨WalkingPair.left⟩
  · rw [← SSet.boundary.ι_ι (0 : Fin 2), Category.assoc, he]
    exact HomotopyFunctionComplex.BoundaryOne.isColimit.fac
      (BinaryCofan.mk s t) ⟨WalkingPair.right⟩

include hi hK in
lemma nonempty_fixedBoundaryHomotopy (f : A ⟶ K) (e₀ e₁ : B ⟶ K)
    (h₀ : i ≫ e₀ = f) (h₁ : i ≫ e₁ = f) :
    Nonempty (RelativeChoiceSpace.FixedBoundaryHomotopy i f e₀ e₁) := by
  obtain ⟨e, hs, ht⟩ := interval i hi hK f
    (RelativeChoiceSpace.ofExtension i f e₀ h₀) (RelativeChoiceSpace.ofExtension i f e₁ h₁)
  change SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ e = _ at hs
  change SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ e = _ at ht
  refine ⟨⟨RelativeChoiceSpace.family i f e, ?_, ?_,
    RelativeChoiceSpace.family_fixed_boundary i f e⟩⟩
  · rw [← RelativeChoiceSpace.family_naturality, hs, RelativeChoiceSpace.family_ofExtension]
  · rw [← RelativeChoiceSpace.family_naturality, ht, RelativeChoiceSpace.family_ofExtension]

end SerrePositivity.SimplicialModel.LocalizedRelativeChoice
