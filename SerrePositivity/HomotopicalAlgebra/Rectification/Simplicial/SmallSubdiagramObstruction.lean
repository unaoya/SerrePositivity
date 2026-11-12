module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneNonempty
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveInitialImage
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLift
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.CodiscreteNerveExtension
public import Mathlib.CategoryTheory.WithTerminal.Basic
public import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.Logic.Small.Basic

/-!
# 中断した任意モデル源への一般化：SmallSubdiagramObstruction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Objectwise homotopical smallness does not give a small natural subdiagram。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0576][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0576
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Objectwise homotopical smallness does not give a small natural subdiagram

A large star has a point at every leaf and a contractible nerve at its hub.
Every pointwise equivalent diagram mapping into it must have a large hub.
A natural quotient to a constant point still exists. This obstructs the
inclusion direction, not small replacement by a natural zigzag.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.SimplicialModel.SmallSubdiagramObstruction
variable (I : Type u)

abbrev Index := WithTerminal (Discrete I)
abbrev hub : Index I := WithTerminal.star
abbrev leaf (i : I) : Index I := WithTerminal.of (Discrete.mk i)
abbrev point : SSet.{u} := SSet.stdSimplex.obj (SimplexCategory.mk 0)

instance : LocallySmall.{0} (Index I) where
  hom_small _ _ := inferInstance

def diagram : Index I ⥤ SSet.{u} :=
  WithTerminal.lift ((Functor.const (Discrete I)).obj point)
    (fun i => SerrePositivity.NerveHomotopy.point (Codiscrete.mk i.as)) (by
      intro i j f
      obtain ⟨i⟩ := i
      obtain ⟨j⟩ := j
      obtain rfl := Discrete.eq_of_hom f
      exact Category.id_comp _)

def label : ((diagram I).obj (hub I)).obj (op (SimplexCategory.mk 0)) → I :=
  fun c => (c.obj 0).as

/-- The counterexample already has Kan values; value-side fibrancy does not fix it. -/
lemma values_kan (i : I) (d : Index I) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from ((diagram I).obj d)) := by
  cases d with
  | of d =>
    change SSet.modelCategoryQuillen.J.rlp (terminal.from point)
    have := isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀ terminalIsTerminal
      (terminal.from point)
    exact (SSet.modelCategoryQuillen.J.rlp).of_isIso _
  | star => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.terminal_horn_rlp i

variable {I} {G : Index I ⥤ SSet.{u}} (α : G ⟶ diagram I)
  (hG : ∀ i, (G.obj (leaf I i)).Nonempty)

def selected (i : I) : (G.obj (hub I)).obj (op (SimplexCategory.mk 0)) :=
  (G.map (WithTerminal.homFrom (Discrete.mk i))).app _ (Classical.choice (hG i))

lemma selected_label (i : I) :
    label I ((α.app (hub I)).app _ (selected hG i)) = i := by
  have hn := congrArg (fun f => label I (f.app (op (SimplexCategory.mk 0))
      (Classical.choice (hG i)))) (α.naturality (WithTerminal.homFrom (Discrete.mk i)))
  exact hn.trans rfl

include α in
lemma selected_injective : Function.Injective (selected hG) := by
  intro i j hij
  have h := congrArg (fun x => label I ((α.app (hub I)).app _ x)) hij
  simpa only [selected_label α hG] using h

include α hG in
lemma index_small_of_hub_small
    (hsmall : Small.{v} ((G.obj (hub I)).obj (op (SimplexCategory.mk 0)))) : Small.{v} I := by
  have := hsmall
  exact small_of_injective (selected_injective α hG)

include α in
lemma index_small_of_localized_comparison
    (hα : ∀ i, IsIso (AnodyneHomotopy.anodyneQ.map (α.app (leaf I i))))
    (hsmall : Small.{v} ((G.obj (hub I)).obj (op (SimplexCategory.mk 0)))) : Small.{v} I := by
  apply index_small_of_hub_small α _ hsmall
  intro i
  exact AnodyneNonempty.nonempty_of_localized_isIso _ (hα i)
    (inferInstanceAs (point.Nonempty))

/-- The obstruction applies even without a monomorphism assumption on the comparison. -/
lemma no_small_natural_source {G : Index (Type v) ⥤ SSet.{v + 1}}
    (α : G ⟶ diagram (Type v))
    (hα : ∀ i, IsIso (AnodyneHomotopy.anodyneQ.map (α.app (leaf (Type v) i)))) :
    ¬ Small.{v} ((G.obj (hub (Type v))).obj (op (SimplexCategory.mk 0))) := by
  intro hsmall
  have := index_small_of_localized_comparison α hα hsmall
  exact not_small_type.{v, 0} this

lemma no_small_diagram_comparison (G : Index (Type v) ⥤ SSet.{v})
    (α : G ⋙ SSet.uliftFunctor.{v + 1, v} ⟶ diagram (Type v))
    (hα : ∀ i, IsIso (AnodyneHomotopy.anodyneQ.map (α.app (leaf (Type v) i)))) : False := by
  apply no_small_natural_source α hα
  change Small.{v} (ULift.{v + 1, v}
    ((G.obj (hub (Type v))).obj (op (SimplexCategory.mk 0))))
  exact small_of_injective (f := ULift.down) ULift.down_injective

def quotient (I : Type u) : diagram I ⟶ (Functor.const (Index I)).obj point where
  app _ := SSet.stdSimplex.isTerminalObj₀.from _
  naturality {_ _} _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- In the opposite direction there is an actual natural pointwise equivalence
to the lift of the constant small point diagram. -/
lemma quotient_isIso (i : I) :
    IsIso (Functor.whiskerRight (quotient I) AnodyneHomotopy.anodyneQ) := by
  have (d : Index I) : IsIso ((Functor.whiskerRight (quotient I)
      AnodyneHomotopy.anodyneQ).app d) := by
    cases d with
    | of d =>
      change IsIso (AnodyneHomotopy.anodyneQ.map
        (SSet.stdSimplex.isTerminalObj₀.from point))
      have he : SSet.stdSimplex.isTerminalObj₀.from point = 𝟙 point :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      rw [he, CategoryTheory.Functor.map_id]
      infer_instance
    | star =>
      let hi : IsInitial (Codiscrete.mk i) :=
        IsInitial.ofUniqueHom (fun _ => ()) (fun _ _ => Subsingleton.elim _ _)
      exact (NerveInitialImage.terminalImageIso hi AnodyneHomotopy.anodyneQ
        (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)).isIso_hom
  exact NatIso.isIso_of_isIso_app _

lemma map_isIso (i : I) {d e : Index I} (f : d ⟶ e) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((diagram I).map f)) := by
  have := quotient_isIso i
  let e := asIso (Functor.whiskerRight (quotient I) AnodyneHomotopy.anodyneQ)
  apply (NatIso.isIso_map_iff e f).mpr
  change IsIso (AnodyneHomotopy.anodyneQ.map (𝟙 point))
  rw [CategoryTheory.Functor.map_id]
  infer_instance

abbrev smallPointDiagram : Index (Type v) ⥤ SSet.{v} :=
  (Functor.const _).obj (SSet.stdSimplex.obj (SimplexCategory.mk 0))

def smallQuotient : diagram (Type v) ⟶ smallPointDiagram ⋙ SSet.uliftFunctor.{v + 1, v} :=
  quotient (Type v) ≫
    { app _ := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIso.{v + 1, v} (SimplexCategory.mk 0)).inv
      naturality {_ _} _ := by ext n x; rfl }

lemma smallQuotient_isIso :
    IsIso (Functor.whiskerRight smallQuotient.{v} AnodyneHomotopy.anodyneQ) := by
  have := quotient_isIso (I := Type v) PUnit
  have (d : Index (Type v)) :
      IsIso ((Functor.whiskerRight smallQuotient.{v} AnodyneHomotopy.anodyneQ).app d) := by
    have : IsIso (AnodyneHomotopy.anodyneQ.map ((quotient (Type v)).app d)) :=
      inferInstanceAs (IsIso ((Functor.whiskerRight (quotient (Type v))
        AnodyneHomotopy.anodyneQ).app d))
    change IsIso (AnodyneHomotopy.anodyneQ.map (_ ≫ _))
    rw [CategoryTheory.Functor.map_comp]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end SerrePositivity.SimplicialModel.SmallSubdiagramObstruction
