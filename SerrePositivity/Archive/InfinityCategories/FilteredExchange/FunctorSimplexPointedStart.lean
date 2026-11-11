module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningSimplexLifts
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying

/-!
概要：関手空間の元の単体の固定始点を、同じ全底上の pointed 持ち上げの初期式へ移す。
方針：元の全図式を展開し、curry の自然性と指定零頂点の式を使う。
規約：単体の全次元を保持。使われ方：三つの元の単位三単体の共通の初期値。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の関手単体を同じ全底上の全単体図式として展開する。 -/
def functorSimplexDiagram {P B X : SSet.{u}} (T : P ⟶ (ihom B).obj X) : P ⊗ B ⟶ X :=
  (β_ P B).hom ≫ uncurry T

/-- 元の関手族の任意のパラメータへの制限は、全底上の展開と厳密に可換する。 -/
lemma functorSimplexDiagram_pre {P P' B X : SSet.{u}}
    (t : P' ⟶ P) (T : P ⟶ (ihom B).obj X) :
    (t ▷ B) ≫ functorSimplexDiagram T = functorSimplexDiagram (t ≫ T) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro p
  rfl

/-- 元の関手単体の初期頂点の式は、全底を保つ単体族の始点式を厳密に与える。 -/
lemma functorSimplexDiagram_initial {B X : SSet.{u}} {n : ℕ} (F : B ⟶ X)
    (T : (Δ[n] : SSet.{u}) ⟶ (ihom B).obj X)
    (h₀ : scaffoldFirstVertex n ≫ T = SSet.const (functorVertex F)) :
    simplexPrismVertex n 0 B ≫ functorSimplexDiagram T = F := by
  have hc := congrArg uncurry h₀
  rw [uncurry_natural_left, uncurry_const_functorVertex] at hc
  have he : simplexPrismVertex n 0 B ≫ (β_ Δ[n] B).hom =
      lift (𝟙 B) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫
        (B ◁ scaffoldFirstVertex n) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext <;> rfl
  rw [functorSimplexDiagram, ← Category.assoc, he, Category.assoc, hc,
    ← Category.assoc, lift_fst, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
