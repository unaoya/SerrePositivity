module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardTopBoundary
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies

/-!
# 標準 Hom の最上位評価と Moore 射影

概要：標準 Hom の最上位成分は退化を消し、Moore 射影で変わらない。
方針：非単射な引き戻しの成分公式と既存の退化消滅判定を使う。
規約：零次数を含めて同じ実射影を使う。計算上限は変更しない。
使われ方：HA 1.2.4、Kerodon 2.5（Tag 00ND）の G10 の指定合成の成分照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory DifferentialGraded AlgebraicTopology.DoldKan
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：最上位評価は退化上で消える。方針：全頂点上の非単射性を使う。
規約：標準 Hom の実退化写像。使われ方：HA 1.2.4 の Moore 射影との照合。 -/
theorem standardTopEval_degeneraciesVanish (x y : D) (n : ℕ) :
    DegeneraciesVanish (n := n) (X := standardModule (R := R) x y)
      (ModuleCat.ofHom (standardTopEval (R := R) x y n)) := by
  cases n with
  | zero => exact (degeneraciesVanish_zero_iff_true _).mpr trivial
  | succ n =>
    rw [degeneraciesVanish_succ_iff]
    change ∀ i : Fin (n + 1), (standardModule (R := R) x y).σ i ≫
      ModuleCat.ofHom (standardTopEval (R := R) x y (n + 1)) = 0
    intro i
    ext f
    change standardTopEval (R := R) x y (n + 1)
      (standardPullback (SimplexCategory.σ i).toOrderHom f) = 0
    unfold standardTopEval
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [standardPullback_val]
    apply MorphismSpaces.pullback_component_of_not_inj
    intro hi
    have h : Function.Injective (SimplexCategory.σ i).toOrderHom := by
      intro a b hab
      exact hi (Finset.mem_univ a) (Finset.mem_univ b) hab
    have hc := Fintype.card_le_of_injective _ h
    simp only [Fintype.card_fin] at hc
    omega

/-- 概要：実 Moore 射影は標準 Hom の最上位成分を保つ。
方針：退化消滅判定で補射影との合成を零にする。
規約：全次数での写像の等式。使われ方：HA 1.2.4 の指定 DK 合成の評価。 -/
theorem standardTopEval_PInfty (x y : D) (n : ℕ) :
    (PInfty (X := standardModule (R := R) x y)).f n ≫
      ModuleCat.ofHom (standardTopEval (R := R) x y n) =
    ModuleCat.ofHom (standardTopEval (R := R) x y n) := by
  have hz := (degeneraciesVanish_iff_QInfty_f_comp _).mp
    (standardTopEval_degeneraciesVanish (R := R) x y n)
  have h := PInfty_f_add_QInfty_f (X := standardModule (R := R) x y) n =≫
    ModuleCat.ofHom (standardTopEval (R := R) x y n)
  simpa only [Preadditive.add_comp, hz, add_zero, Category.id_comp] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
