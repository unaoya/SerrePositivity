module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.SimplicialCuts
public import SerrePositivity.EInfinity.BarrattEccles.Normalized
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Alexander–Whitney の非正規化成分

概要：Berger–Fresse §1.1.4 の AW 対角の各次数成分を自由加群上に構成する。
方針：前半と後半の面の純テンソルを標準生成元から線形延長する。
規約：この段階では退化単体も残し、鎖写像の条件と正規化への降下は別に証明する。
使われ方：正規化対角の生成元公式と、その自然性・余結合性の入力となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.Simplicial _root_.TensorProduct

variable (A : Type u) [CommRing A]

/-- 概要：単体集合の n 単体上の自由加群（Berger–Fresse §1.1.4）。
方針：既存の線形化関手の n 次数を取る。
規約：添字の宇宙を基礎環と同じ宇宙へ持ち上げる。
使われ方：非正規化 AW 成分の始域と終域を表す。 -/
abbrev simplexModule (X : SSet.{0}) (n : ℕ) : ModuleCat A :=
  (ModuleCat.free A).obj (ULift.{u} (X _⦋n⦌))

private lemma linearization_map_freeMk {X Y : SSet.{0}} (f : X ⟶ Y) (n : ℕ)
    (x : X _⦋n⦌) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map f).app _ (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (f.app _ x)) := ModuleCat.free_map_apply _ _

/-- 概要：非正規化 AW 対角の (p,q) 成分（Berger–Fresse §1.1.4）。
方針：単体 x を x[0,…,p] ⊗ x[p,…,p+q] に送って線形延長する。
規約：p+q=n を明示し、切断の頂点番号を固定する。
使われ方：正規化対角の成分を構成する前段階となる。 -/
def rawComponent (X : SSet.{0}) (n p q : ℕ) (h : p + q = n) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexModule A X n ⟶ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexModule A X p ⊗ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexModule A X q :=
  ModuleCat.freeDesc (↾fun x : ULift.{u} (X _⦋n⦌) =>
    ModuleCat.freeMk (ULift.up (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x.down 0 p (by omega))) ⊗ₜ[A]
      ModuleCat.freeMk (ULift.up (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x.down p q (by omega))))

/-- 概要：AW 成分の標準生成元上の値（Berger–Fresse §1.1.4）。
方針：自由加群の線形延長の評価公式を使う。
規約：退化単体も許す。
使われ方：対角の性質を単体の切断の等式に帰着する。 -/
@[simp] lemma rawComponent_freeMk (X : SSet.{0}) (n p q : ℕ) (h : p + q = n)
    (x : X _⦋n⦌) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.rawComponent A X n p q h (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x 0 p (by omega))) ⊗ₜ[A]
        ModuleCat.freeMk (ULift.up (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x p q (by omega))) :=
  ModuleCat.freeDesc_apply _ _

/-- 概要：非正規化 AW 成分は単体集合の射に自然（Berger–Fresse §1.1.4）。
方針：自由生成元で検査し、切断の自然性を二つの因子に適用する。
規約：単体集合の射は次数を変えない。
使われ方：単体的合成を線形化した射と AW 対角の可換性を与える。 -/
lemma rawComponent_natural {X Y : SSet.{0}} (f : X ⟶ Y)
    (n p q : ℕ) (h : p + q = n) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map f).app _ ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.rawComponent A Y n p q h =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.rawComponent A X n p q h ≫
        (((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map f).app _ ⊗ₘ
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map f).app _) := by
  apply ModuleCat.free_hom_ext
  intro ⟨x⟩
  simp only [ModuleCat.comp_apply]
  erw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.linearization_map_freeMk A f n x, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.rawComponent_freeMk A Y n p q h,
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.rawComponent_freeMk A X n p q h, ModuleCat.MonoidalCategory.tensorHom_tmul]
  erw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.linearization_map_freeMk A f p (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x 0 p (by omega)),
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.linearization_map_freeMk A f q (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x p q (by omega))]
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_natural f x 0 p (by omega), _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_natural f x p q (by omega)]

/-- 概要：非正規化 AW 成分は三つの次数への分割について余結合的（Berger–Fresse §1.1.4）。
方針：自由生成元で三つの区間への反復切断を一度の切断へ戻す。
規約：最終的なテンソルの括弧は右結合とし、加法の移送を明示する。
使われ方：正規化対角の余結合性の各三重次数成分を与える。 -/
lemma rawComponent_coassoc (X : SSet.{0}) (p q r : ℕ) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.rawComponent A X (p + q + r) (p + q) r rfl ≫
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.rawComponent A X (p + q) p q rfl ▷ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexModule A X r) ≫
        (α_ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexModule A X p) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexModule A X q) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexModule A X r)).hom =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.rawComponent A X (p + q + r) p (q + r) (Nat.add_assoc p q r).symm ≫
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexModule A X p ◁ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.rawComponent A X (q + r) q r rfl) := by
  apply ModuleCat.free_hom_ext
  intro ⟨x⟩
  simp only [ModuleCat.comp_apply, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.rawComponent_freeMk,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply,
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.rawComponent_freeMk,
    ModuleCat.MonoidalCategory.associator_hom_apply]
  simp only [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_cut, zero_add, add_zero]

end SerrePositivity.SimplicialChains.AlexanderWhitney
