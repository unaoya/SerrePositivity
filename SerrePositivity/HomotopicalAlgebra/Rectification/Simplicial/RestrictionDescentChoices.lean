module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanRestrictionEquivalence
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanLocalizedComparisonResolution
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceSpace
public import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
# 中断した任意モデル源への一般化：RestrictionDescentChoices

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual spaces of descent choices with relative parameter extension。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0545][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0545
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual spaces of descent choices with relative parameter extension

A point decodes to a map on the target of the original equivalence and a
comparison interval on its source. One interval on the entire resolution
makes all parameter restrictions compatible. The choice space need not
be small in a lower value universe.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.RestrictionDescentChoices
variable {A B K : SSet.{v}} (a : A ⟶ B)
  (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

abbrev restriction : (ihom B).obj K ⟶ (ihom A).obj K := (pre a).app K
abbrev resolution : SSet.{v} := KanLocalizedComparisonResolution.obj (restriction (K := K) a)
abbrev projection : resolution (K := K) a ⟶ (ihom A).obj K :=
  KanLocalizedComparisonResolution.projection (restriction (K := K) a)

def decode : resolution (K := K) a ⟶ (ihom B).obj K :=
  KanLocalizedComparisonResolution.decode (restriction (K := K) a)
    (SimplexParameterHom.native_kan B K hK) (KanRestrictionEquivalence.localized_isIso a ha hK)

abbrev comparison : SSet.Homotopy (decode a ha hK ≫ restriction a) (projection a) :=
  KanLocalizedComparisonResolution.comparison (restriction (K := K) a)
    (SimplexParameterHom.native_kan B K hK) (SimplexParameterHom.native_kan A K hK)
    (KanRestrictionEquivalence.localized_isIso a ha hK)

abbrev obj (h : A ⟶ K) : SSet.{v} := pullback (projection a) (RelativeChoiceSpace.name h)
abbrev inclusion (h : A ⟶ K) : obj a h ⟶ resolution (K := K) a := pullback.fst _ _
abbrev toPoint (h : A ⟶ K) : obj a h ⟶ SSet.stdSimplex.obj (SimplexCategory.mk 0) :=
  pullback.snd _ _

lemma over (h : A ⟶ K) : inclusion a h ≫ projection a =
    toPoint a h ≫ RelativeChoiceSpace.name h := pullback.condition

lemma toPoint_mono_rlp (h : A ⟶ K) :
    (MorphismProperty.monomorphisms SSet.{v}).rlp (toPoint a h) := by
  exact (MorphismProperty.monomorphisms SSet.{v}).rlp.pullback_snd
    (projection a) (RelativeChoiceSpace.name h)
    (KanLocalizedComparisonResolution.projection_mono_rlp (restriction (K := K) a))

lemma parameter_extension (h : A ⟶ K) {U V : SSet.{v}} (j : U ⟶ V) [Mono j]
    (c : U ⟶ obj a h) : ∃ e : V ⟶ obj a h, j ≫ e = c := by
  have : HasLiftingProperty j (toPoint a h) := toPoint_mono_rlp a h j inferInstance
  let sq : CommSq c j (toPoint a h) (SSet.stdSimplex.isTerminalObj₀.from V) :=
    ⟨SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

lemma terminal_mono_rlp (h : A ⟶ K) : (MorphismProperty.monomorphisms SSet.{v}).rlp
    (terminal.from (obj a h)) := by
  intro U V j hj
  have : Mono j := hj
  constructor
  intro c b sq
  obtain ⟨e, he⟩ := parameter_extension a h j c
  exact CommSq.HasLift.mk' { l := e, fac_left := he, fac_right := terminal.hom_ext _ _ }

lemma boundary_rlp (h : A ⟶ K) : SSet.modelCategoryQuillen.I.rlp
    (terminal.from (obj a h)) := by
  rw [← SSet.rlp_monomorphisms]
  exact terminal_mono_rlp a h

lemma kan (h : A ⟶ K) : SSet.modelCategoryQuillen.J.rlp (terminal.from (obj a h)) := by
  intro U V j hj
  exact terminal_mono_rlp a h j (SSet.modelCategoryQuillen.J_le_monomorphisms j hj)

def decoded {T : SSet.{v}} (h : A ⟶ K) (c : T ⟶ obj a h) : T ⟶ (ihom B).obj K :=
  c ≫ inclusion a h ≫ decode a ha hK

def family {T : SSet.{v}} (h : A ⟶ K) (c : T ⟶ obj a h) : B ⊗ T ⟶ K :=
  uncurry (decoded a ha hK h c)

lemma family_naturality {T U : SSet.{v}} (h : A ⟶ K) (c : T ⟶ obj a h) (j : U ⟶ T) :
    family a ha hK h (j ≫ c) = B ◁ j ≫ family a ha hK h c := by
  unfold family decoded
  rw [Category.assoc, uncurry_natural_left]

def parameterComparison {T : SSet.{v}} (h : A ⟶ K) (c : T ⟶ obj a h) :
    SSet.Homotopy (decoded a ha hK h c ≫ restriction a)
      (c ≫ toPoint a h ≫ RelativeChoiceSpace.name h) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints
    (HomotopyClasses.preHomotopy (c ≫ inclusion a h) (comparison a ha hK))
    (Category.assoc _ _ _) (by rw [Category.assoc, over])

lemma parameterComparison_naturality {T U : SSet.{v}} (h : A ⟶ K)
    (c : T ⟶ obj a h) (j : U ⟶ T) :
    (parameterComparison a ha hK h (j ≫ c)).h =
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
        (parameterComparison a ha hK h c).h := by
  simp only [parameterComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h]
  change ((j ≫ c) ≫ inclusion a h) ▷ _ ≫ _ = _
  rw [Category.assoc, comp_whiskerRight, Category.assoc]
  rfl

def familyComparison {T : SSet.{v}} (h : A ⟶ K) (c : T ⟶ obj a h) :
    SSet.Homotopy (a ▷ T ≫ family a ha hK h c)
      (uncurry (c ≫ toPoint a h ≫ RelativeChoiceSpace.name h)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints
    (HomotopyClassesClosed.uncurryHomotopy (parameterComparison a ha hK h c))
    (by rw [uncurry_pre_app]; rfl) rfl

lemma relative_extension (h : A ⟶ K) {U V : SSet.{v}} (j : U ⟶ V) [Mono j]
    (c : U ⟶ obj a h) : ∃ e : V ⟶ obj a h,
      j ≫ e = c ∧ B ◁ j ≫ family a ha hK h e = family a ha hK h c ∧
        j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
          (parameterComparison a ha hK h e).h = (parameterComparison a ha hK h c).h := by
  obtain ⟨e, he⟩ := parameter_extension a h j c
  refine ⟨e, he, ?_, ?_⟩
  · rw [← family_naturality, he]
  · rw [← parameterComparison_naturality, he]

end SerrePositivity.SimplicialModel.RestrictionDescentChoices
