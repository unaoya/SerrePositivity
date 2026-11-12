module

public import SerrePositivity.HomotopicalAlgebra.Quillen.Saturation
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Fibrant な試験終域への局所化 Hom による弱同値の検出

概要：Hovey §1.2 の局所化 Hom の前合成を fibrant 終域だけで試験して弱同値を検出する。
方針：両対象を fibrant 置換し、全単射から局所化後の逆を作る。
規約：始域の cofibrancy・関手的置換・単体集合のモデル構造は不要。
使われ方：重み付き frame の錐空間から実現の弱同値性を導く。
-/

@[expose] public section

noncomputable section

universe u v

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

open CategoryTheory Limits HomotopicalAlgebra

variable {C : Type v} [Category.{u} C] [ModelCategory C]

/-- 概要：fibrant 終域への局所化 Hom の全単射性は弱同値を検出する（Hovey §1.2）。
方針：fibrant 置換への Hom で逆と両合成式を得て、モデルの飽和性を使う。
規約：元の射と標準の普通の局所化を使う。
使われ方：一般 homotopy 極限の計算関手の擬同型不変性。 -/
lemma weakEquivalence_of_localized_precomposition_fibrant {X Y : C} (f : X ⟶ Y)
    (h : let Q := (weakEquivalences C).Q
      ∀ Z : C, IsFibrant Z → Function.Bijective
        (fun g : Q.obj Y ⟶ Q.obj Z => Q.map f ≫ g)) : weakEquivalences C f := by
  let Q := (weakEquivalences C).Q
  let x := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
    (terminal.from X)
  let y := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
    (terminal.from Y)
  have : Fibration x.p := ⟨x.hp⟩
  have : Fibration y.p := ⟨y.hp⟩
  have hx : IsFibrant x.Z := (isFibrant_iff_of_isTerminal x.p terminalIsTerminal).mpr
    inferInstance
  have hy : IsFibrant y.Z := (isFibrant_iff_of_isTerminal y.p terminalIsTerminal).mpr
    inferInstance
  have : IsIso (Q.map x.i) := Localization.inverts Q (weakEquivalences C) _ x.hi.2
  have : IsIso (Q.map y.i) := Localization.inverts Q (weakEquivalences C) _ y.hi.2
  obtain ⟨g₀, hg₀⟩ := (h x.Z hx).surjective (Q.map x.i)
  change Q.map f ≫ g₀ = Q.map x.i at hg₀
  let g := g₀ ≫ inv (Q.map x.i)
  have hfg : Q.map f ≫ g = 𝟙 _ := by
    dsimp only [g]
    rw [← Category.assoc, hg₀, IsIso.hom_inv_id]
  have hgf : g ≫ Q.map f = 𝟙 _ := by
    apply (cancel_mono (Q.map y.i)).mp
    apply (h y.Z hy).injective
    simp only [Category.assoc, Category.id_comp]
    rw [← Category.assoc (Q.map f) g, hfg, Category.id_comp]
  have : IsIso (Q.map f) := ⟨g, hfg, hgf⟩
  exact (SerrePositivity.Quillen.weakEquivalences_iff_isIso_map Q f).mpr inferInstance

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
