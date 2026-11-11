module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallSimplicialValue
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftAnodyneReflection

/-!
# 中断した任意モデル源への一般化：SmallDiagramQuotient

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A strict small quotient diagram with a natural localized comparison。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0571][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0571
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A strict small quotient diagram with a natural localized comparison

The inputs are a stable degreewise congruence, actual smallness of its
quotient types, and finite boundary lifting for the quotient projections.
No large simplicial model structure or smallness of the base is assumed.
-/

@[expose] public section
universe v w uD vD uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.SimplicialModel.SmallDiagramQuotient
variable {D : Type uD} [Category.{vD} D] {F : D ⥤ SSet.{max w v}}
  (R : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.Congruence F)
  (hsmall : ∀ d n, Small.{v} (Quotient (R.rel d n)))

lemma total_small (d : D) (n : SimplexCategoryᵒᵖ) :
    Small.{v} (Quotient ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.total F).rel d n)) := by
  have : Subsingleton (Quotient ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.total F).rel d n)) :=
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.total_subsingleton d n
  infer_instance

/-- Total erasure preserves homotopy only with an additional lifting certificate. -/
lemma total_boundary_rlp (F : D ⥤ SSet.{w}) (d : D)
    (hF : (MorphismProperty.monomorphisms SSet.{w}).rlp (terminal.from (F.obj d))) :
    SSet.modelCategoryQuillen.I.rlp ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.projection
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.total F)).app d) := by
  rw [← SSet.rlp_monomorphisms]
  intro A B j hj
  have : HasLiftingProperty j (terminal.from (F.obj d)) := hF j hj
  refine ⟨fun {a b} _ => ?_⟩
  let sq : CommSq a j (terminal.from (F.obj d)) (terminal.from B) :=
    ⟨terminal.hom_ext _ _⟩
  refine ⟨⟨{ l := sq.lift, fac_left := sq.fac_left, fac_right := ?_ }⟩⟩
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.total_subsingleton (F := F) d n).elim _ _

abbrev functor : D ⥤ SSet.{v} :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.shrinkDiagram (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.functor R) hsmall

def projection : F ⟶ functor R hsmall ⋙ SSet.uliftFunctor.{max w v, v} :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.projection R ≫
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.diagramLiftIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.functor R) hsmall).inv

variable (hboundary : ∀ d, SSet.modelCategoryQuillen.I.rlp
  ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.projection R).app d))

include hboundary in
lemma projection_mono_rlp (d : D) :
    (MorphismProperty.monomorphisms SSet.{max w v}).rlp ((projection R hsmall).app d) := by
  have hp : (MorphismProperty.monomorphisms SSet.{max w v}).rlp
      ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.projection R).app d) := by
    rw [SSet.rlp_monomorphisms]
    exact hboundary d
  exact (MorphismProperty.monomorphisms _).rlp.comp_mem _ _ hp
    ((MorphismProperty.monomorphisms _).rlp.of_isIso _)

def imageIso {H : Type uH} [Category.{vH} H] (L : SSet.{max w v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    F ⋙ L ≅ (functor R hsmall ⋙ SSet.uliftFunctor.{max w v, v}) ⋙ L := by
  have (d : D) : IsIso ((Functor.whiskerRight (projection R hsmall) L).app d) :=
    MonoRightLiftingContraction.image_isIso _ (projection_mono_rlp R hsmall hboundary d) L hL
  have : IsIso (Functor.whiskerRight (projection R hsmall) L) := NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerRight (projection R hsmall) L)

include hboundary in
lemma lifted_kan (d : D)
    (hF : SSet.modelCategoryQuillen.J.rlp (terminal.from (F.obj d))) :
    SSet.modelCategoryQuillen.J.rlp
      (terminal.from (SSet.uliftFunctor.{max w v, v}.obj ((functor R hsmall).obj d))) := by
  let p := (projection R hsmall).app d
  obtain ⟨s, hs⟩ := MonoRightLiftingContraction.exists_section p
    (projection_mono_rlp R hsmall hboundary d)
  let r : RetractArrow (terminal.from (SSet.uliftFunctor.obj ((functor R hsmall).obj d)))
      (terminal.from (F.obj d)) :=
    { i := Arrow.homMk s (𝟙 _) (terminal.hom_ext _ _)
      r := Arrow.homMk p (𝟙 _) (terminal.hom_ext _ _)
      retract := by ext <;> simp [hs] }
  exact MorphismProperty.of_retract r hF

include hboundary in
lemma kan (d : D) (hF : SSet.modelCategoryQuillen.J.rlp (terminal.from (F.obj d))) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from ((functor R hsmall).obj d)) := by
  let U := SSet.uliftFunctor.{max w v, v}
  let e := (terminalIsTerminal.isTerminalObj U).uniqueUpToIso terminalIsTerminal
  let a : Arrow.mk (U.map (terminal.from ((functor R hsmall).obj d))) ≅
      Arrow.mk (terminal.from (U.obj ((functor R hsmall).obj d))) :=
    Arrow.isoMk (Iso.refl _) e (terminal.hom_ext _ _)
  apply (UniverseLift.horn_rightClass_iff.{max w v, v}
    (terminal.from ((functor R hsmall).obj d))).mp
  exact (SSet.modelCategoryQuillen.J.rlp.arrow_iso_iff a).mpr
    (lifted_kan R hsmall hboundary d hF)

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hboundary hcof hfib in
lemma map_weakEquivalence {d e : D} (f : d ⟶ e)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map (F.map f))) :
    weakEquivalences SSet.{v} ((functor R hsmall).map f) := by
  apply (UniverseLift.weakEquivalences_iff_lift_anodyneQ_isIso hcof hfib _).mpr
  exact (NatIso.isIso_map_iff (imageIso R hsmall hboundary AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)) f).mp hf

end SerrePositivity.SimplicialModel.SmallDiagramQuotient
