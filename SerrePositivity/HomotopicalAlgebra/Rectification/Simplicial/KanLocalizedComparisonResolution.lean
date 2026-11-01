module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoLocalizedFactorization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoStrictExtension
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoRelativeHomotopy

/-!
# 中断した任意モデル源への一般化：KanLocalizedComparisonResolution

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A relative comparison resolution with one global decoding homotopy。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0416][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0416
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A relative comparison resolution with one global decoding homotopy

Every prescribed parameter boundary lifts strictly. Decoding preserves it,
and one global interval supplies all comparison homotopies simultaneously.
No model structure is used in the value universe.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.KanLocalizedComparisonResolution
variable {X Y : SSet.{v}} (f : X ⟶ Y)
  (hX : SSet.modelCategoryQuillen.J.rlp (terminal.from X))
  (hY : SSet.modelCategoryQuillen.J.rlp (terminal.from Y))
  (hf : IsIso (AnodyneHomotopy.anodyneQ.map f))

abbrev obj : SSet.{v} := MonoLocalizedFactorization.middle f
abbrev unit : X ⟶ obj f := MonoLocalizedFactorization.left f
abbrev projection : obj f ⟶ Y := MonoLocalizedFactorization.right f

lemma unit_projection : unit f ≫ projection f = f := MonoLocalizedFactorization.fac f

include hf in
lemma unit_localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map (unit f)) :=
  (MonoLocalizedFactorization.left_localized_isIso_iff f).mpr hf

def decode : obj f ⟶ X :=
  (KanMonoStrictExtension.exists_extension (unit f) hX (unit_localized_isIso f hf) (𝟙 X)).choose

lemma unit_decode : unit f ≫ decode f hX hf = 𝟙 X :=
  (KanMonoStrictExtension.exists_extension (unit f) hX (unit_localized_isIso f hf)
    (𝟙 X)).choose_spec

def boundaryHomotopy : SSet.Homotopy
    (unit f ≫ (decode f hX hf ≫ f)) (unit f ≫ projection f) where
  h := fst X (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ f
  h₀ := by
    rw [← Category.assoc, SSet.ι₀_fst, Category.id_comp, ← Category.assoc,
      unit_decode, Category.id_comp]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp, unit_projection]
    rfl
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

include hY in
def comparisonData :
    { H : SSet.Homotopy (decode f hX hf ≫ f) (projection f) //
      unit f ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h =
        fst X (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ f } := by
  let h := KanMonoRelativeHomotopy.exists_extension
    (unit f) (unit_localized_isIso f hf) hY _ _ (boundaryHomotopy f hX hf)
  exact ⟨h.choose, h.choose_spec⟩

abbrev comparison := (comparisonData f hX hY hf).val

lemma comparison_on_unit :
    unit f ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ (comparison f hX hY hf).h =
      fst X (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ f :=
  (comparisonData f hX hY hf).property

lemma projection_mono_rlp : (MorphismProperty.monomorphisms SSet.{v}).rlp (projection f) :=
  MonoLocalizedFactorization.right_all_mono_rlp f

lemma parameter_extension {U V : SSet.{v}} (j : U ⟶ V) [Mono j]
    (c : U ⟶ obj f) (b : V ⟶ Y) (hc : c ≫ projection f = j ≫ b) :
    ∃ e : V ⟶ obj f, j ≫ e = c ∧ e ≫ projection f = b := by
  have : HasLiftingProperty j (projection f) := projection_mono_rlp f j inferInstance
  let sq : CommSq c j (projection f) b := ⟨hc⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

def parameterComparison {T : SSet.{v}} (c : T ⟶ obj f) :
    SSet.Homotopy (c ≫ decode f hX hf ≫ f) (c ≫ projection f) :=
  HomotopyClasses.preHomotopy c (comparison f hX hY hf)

lemma parameterComparison_naturality {T U : SSet.{v}} (c : T ⟶ obj f) (j : U ⟶ T) :
    (parameterComparison f hX hY hf (j ≫ c)).h =
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
        (parameterComparison f hX hY hf c).h := by
  change (j ≫ c) ▷ _ ≫ _ = _
  rw [comp_whiskerRight, Category.assoc]
  rfl

end SerrePositivity.SimplicialModel.KanLocalizedComparisonResolution
