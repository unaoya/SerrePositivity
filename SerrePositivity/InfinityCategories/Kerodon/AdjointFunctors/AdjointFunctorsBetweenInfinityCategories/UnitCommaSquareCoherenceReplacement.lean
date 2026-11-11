module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.CommaSquareUncurry

/-!
概要：comma 正方形の標的を保ち、同じ四辺を持つ関手正方形から coherence を置き換える。
方針：関手正方形を uncurry して二重区間のホモトピーへ戻す。
規約：四辺の代表と Y 側の標的図式を保持する。
使われ方：B1 の時間付きパラメータ上での comma 正方形の構成。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

section
variable {A X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
variable {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A)

/-- 概要：comma 正方形の四辺を関手ホモトピーとして束ねる。
方針：既存の関手正方形と四辺の計算を組にする。
規約：元の図式そのものを保持する。
使われ方：標的を固定した coherence の置き換えの型。 -/
noncomputable def UnitCommaFiberSquare.compositionSquare :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (SSet.const v : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x))
      s.targetHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (SSet.const w : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)) :=
  ⟨s.functorSquare, s.functorSquare_bottom, s.functorSquare_top,
    s.functorSquare_left, s.functorSquare_right⟩

variable (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (SSet.const v : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)) s.targetHomotopy
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (SSet.const w : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)))

/-- 概要：同じ四辺の関手正方形から元の標的へ向かう coherence を復元する。
方針：正方形の uncurry の終点を二重交換で元の標的の G 像と照合する。
規約：raw な円柱の射は正方形の uncurry そのもの。
使われ方：coherence だけを置き換えた comma 正方形。 -/
noncomputable def UnitCommaFiberSquare.replacementCoherence :
    SSet.Homotopy (SSet.const x : (Δ[1] : SSet.{u}) ⊗ A ⟶ X) (s.target ≫ G) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.functorSquareCoherence Q).h
  h₀ := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.functorSquareCoherence Q).h₀
  h₁ := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.functorSquareCoherence Q).h₁.trans
    change (β_ (Δ[1] : SSet.{u}) A).hom ≫
      ((β_ A (Δ[1] : SSet.{u})).hom ≫ s.target ≫ G) = _
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：標的と側辺を保持して関手正方形から comma 正方形を復元する。
方針：復元した coherence に元の標的の両端条件と正方形の側辺の公式を添える。
規約：Y 側の標的は元の s.target。
使われ方：時間パラメータを加えた関手正方形の族への変換。 -/
noncomputable def UnitCommaFiberSquare.withFunctorSquare : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x v w A where
  target := s.target
  coherence := s.replacementCoherence Q
  target_zero := s.target_zero
  target_one := s.target_one
  coherence_zero := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.functorSquareCoherence_left Q
  coherence_one := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.functorSquareCoherence_right Q

/-- 概要：coherence を置き換えた正方形の関手表示は指定した図式そのもの。
方針：uncurry と座標交換の両逆を使う。
規約：ホモトピー類だけでなく図式を厳密に回収する。
使われ方：時間端点と境界の検証。 -/
lemma UnitCommaFiberSquare.withFunctorSquare_functorSquare :
    (s.withFunctorSquare Q).functorSquare = Q.diagram := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.functorSquareCoherence_recover Q

end

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
