module

public import SerrePositivity.KST.Spectra.CosimplicialHornFibration
public import SerrePositivity.KST.Spectra.KanCompositeCancellation

/-!
概要：余単体図式の射を anodyne な比較と二つの Reedy fibration へ分解する。
方針：射と恒等射の積への図式を horn 因子分解する。
規約：合成と切断の等式は厳密。元の図式の Reedy 条件は射影の充填でだけ使う。
使われ方：Goerss–Jardine VII §4、VIII §1。通常の Tot の係数の同型保存。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SSet SSet.modelCategoryQuillen
open SerrePositivity.Reedy
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.CosimplicialTwoProjections

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : CosimplicialObject SSet.{u}} (f : X ⟶ Y)

/-- 概要：射と恒等射を成分とする積への図式。
方針：始域を第二成分として保持する。
規約：終域は余単体図式の圏での積。
使われ方：Goerss–Jardine VII §4。二射影の分解の入力。 -/
abbrev input : Arrow (CosimplicialObject SSet.{u}) := Arrow.mk (prod.lift f (𝟙 X))

/-- 概要：二射影の分解の中間余単体図式。
方針：積への射の horn 因子分解の中間を取る。
規約：基礎関手的因子分解をそのまま使う。
使われ方：Goerss–Jardine VII §4。Tot の係数比較の中間対象。 -/
abbrev obj : CosimplicialObject SSet.{u} :=
  CosimplicialHornFactorization.factorization.Z.obj (input f)

/-- 概要：元の始域から中間図式への実際の比較。
方針：horn 因子分解の左射を取る。
規約：相対 latching anodyne。
使われ方：Goerss–Jardine VII §4。二射影の共通の切断。 -/
abbrev inclusion : X ⟶ obj f :=
  CosimplicialHornFactorization.factorization.i.app (input f)

/-- 概要：元の始域への第二射影。
方針：因子分解の右射の第二成分を取る。
規約：比較射との合成は恒等射。
使われ方：Goerss–Jardine VIII §1。Tot の射の切断による検出。 -/
def sourceProjection : obj f ⟶ X :=
  CosimplicialHornFactorization.factorization.p.app (input f) ≫ prod.snd

/-- 概要：元の終域への第一射影。
方針：因子分解の右射の第一成分を取る。
規約：比較射との合成は元の射。
使われ方：Goerss–Jardine VIII §1。Tot の射の因子分解。 -/
def targetProjection : obj f ⟶ Y :=
  CosimplicialHornFactorization.factorization.p.app (input f) ≫ prod.fst

@[reassoc (attr := simp)]
lemma inclusion_sourceProjection : inclusion f ≫ sourceProjection f = 𝟙 X := by
  rw [sourceProjection, ← Category.assoc, inclusion,
    CosimplicialHornFactorization.factorization.fac_app]
  exact prod.lift_snd _ _

@[reassoc (attr := simp)]
lemma inclusion_targetProjection : inclusion f ≫ targetProjection f = f := by
  rw [targetProjection, ← Category.assoc, inclusion,
    CosimplicialHornFactorization.factorization.fac_app]
  exact prod.lift_fst _ _

lemma inclusion_anodyne (j : SimplexCategory) : anodyneExtensions ((inclusion f).app j) :=
  CosimplicialHornFactorization.left_app _
    (CosimplicialHornFactorization.factorization.hi (input f)) j

lemma sourceProjection_reedy
    (hY : reedyRight simplex J.rlp (terminal.from Y)) :
    reedyRight simplex J.rlp (sourceProjection f) :=
  CosimplicialHornFibration.comp _ _
    (CosimplicialHornFactorization.factorization.hp (input f))
    (CosimplicialHornFibration.prod_snd Y X hY)

lemma targetProjection_reedy
    (hX : reedyRight simplex J.rlp (terminal.from X)) :
    reedyRight simplex J.rlp (targetProjection f) :=
  CosimplicialHornFibration.comp _ _
    (CosimplicialHornFactorization.factorization.hp (input f))
    (CosimplicialHornFibration.prod_fst Y X hX)

/-- 概要：元の図式が Reedy Kan なら中間図式も Reedy Kan。
方針：始域への射影と始域の終射を合成する。
規約：両図式の終射の Reedy 条件を明示する。
使われ方：Goerss–Jardine VII §4、VIII §1。中間 Tot の Kan 性。 -/
lemma obj_reedy
    (hX : reedyRight simplex J.rlp (terminal.from X))
    (hY : reedyRight simplex J.rlp (terminal.from Y)) :
    reedyRight simplex J.rlp (terminal.from (obj f)) := by
  have h := CosimplicialHornFibration.comp (sourceProjection f) (terminal.from X)
    (sourceProjection_reedy f hY) hX
  have he : sourceProjection f ≫ terminal.from X = terminal.from (obj f) := terminal.hom_ext _ _
  rwa [he] at h

/-- 概要：元の各値が Kan なら中間図式の各値も Kan。
方針：始域への射影の各段の horn RLP を使う。
規約：終域の Reedy 条件は射影の充填に用いる。
使われ方：Goerss–Jardine VII §4。中間図式の π_* の定義。 -/
lemma obj_kanComplex [∀ j, KanComplex (X.obj j)]
    (hY : reedyRight simplex J.rlp (terminal.from Y)) (j : SimplexCategory) :
    KanComplex ((obj f).obj j) := by
  have hp := CosimplicialHornFactorization.right_app (sourceProjection f)
    (sourceProjection_reedy f hY) j
  let : Fibration ((sourceProjection f).app j) :=
    (modelCategoryQuillen.fibration_iff _).mpr hp
  exact isFibrant_of_fibration ((sourceProjection f).app j)

end

end SerrePositivity.KST.Spectra.CosimplicialTwoProjections
