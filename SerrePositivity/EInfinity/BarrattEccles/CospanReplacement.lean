module

public import SerrePositivity.EInfinity.BarrattEccles.PullbackQuillen
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# E 代数の cospan の fibration 置換と底での引き戻し

概要：BM 命題 4.1・Hovey §1.3 の右導来引き戻しを具体的な置換で計算する。
方針：左脚を trivial cofibration と fibration に分解し、右脚との引き戻しを取る。
規約：全対象が fibrant である具体的な E 代数のモデル構造を使う。
使われ方：E2a-4 の homotopy 引き戻しと E2b の忘却後の比較。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits HomotopicalAlgebra

variable (A : Type u) [CommRing A]

/-- 概要：E 代数射の左脚を fibration に置き換える（Hovey §1.3）。
方針：実際の転送モデル構造の trivial cofibration・fibration 分解を選ぶ。
規約：モデル構造の存在を入力仮定にしない。
使われ方：slice の fibrant 置換と homotopy 引き戻しの対象。 -/
def fibrationReplacement {X Z : (operad A).Algebra} (f : X ⟶ Z) :
    let := modelCategory A
    MorphismProperty.MapFactorizationData (trivialCofibrations (operad A).Algebra)
      (fibrations (operad A).Algebra) f := by
  let := modelCategory A
  exact MorphismProperty.factorizationData _ _ f

/-- 概要：左脚置換の包含は底の擬同型（BM 命題 4.1）。
方針：trivial cofibration の弱同値成分を具体的な判定へ移す。
規約：任意の E 代数射。
使われ方：元の cospan と置換 cospan の弱同値。 -/
lemma fibrationReplacement_quasiIso {X Z : (operad A).Algebra} (f : X ⟶ Z) :
    QuasiIso (fibrationReplacement A f).i.hom := by
  let := modelCategory A
  exact (weakEquivalence_iff A _).mp ⟨(fibrationReplacement A f).hi.2⟩

/-- 概要：置換の射影は各整数次数で全射（BM 命題 4.1）。
方針：分解の fibration 成分を具体的な判定へ移す。
規約：底の複体の全整数次数。
使われ方：忘却後も正しい fibration 置換であることの保証。 -/
lemma fibrationReplacement_surjective {X Z : (operad A).Algebra} (f : X ⟶ Z) :
    ∀ n : ℤ, Function.Surjective ((fibrationReplacement A f).p.hom.f n) := by
  let := modelCategory A
  exact (fibration_iff A _).mp ⟨(fibrationReplacement A f).hp⟩

/-- 概要：左脚置換を底を固定した slice の対象にする（Hovey §1.3）。
方針：置換の射影を Over の対象として読む。
規約：基底 Z は変えない。
使われ方：右導来関手の fibrant 計算点。 -/
def replacementOver {X Z : (operad A).Algebra} (f : X ⟶ Z) : Over Z :=
  Over.mk (fibrationReplacement A f).p

/-- 概要：元の左脚から置換への slice 射（Hovey §1.3）。
方針：分解の三角形によって包含を底 Z 上の射にする。
規約：基底は恒等で固定する。
使われ方：元の cospan と fibrant 置換の局所化での比較。 -/
def replacementInclusion {X Z : (operad A).Algebra} (f : X ⟶ Z) :
    Over.mk f ⟶ replacementOver A f :=
  Over.homMk (fibrationReplacement A f).i (fibrationReplacement A f).fac

/-- 概要：左脚の包含は slice の弱同値（BM 命題 4.1）。
方針：忘却後の擬同型性を slice の弱同値判定へ移す。
規約：具体的な E のモデル構造を局所的に選ぶ。
使われ方：導来引き戻しを元の左脚の値として読む。 -/
lemma replacementInclusion_weakEquivalence {X Z : (operad A).Algebra} (f : X ⟶ Z) :
    let := modelCategory A
    WeakEquivalence (replacementInclusion A f) := by
  let := modelCategory A
  change WeakEquivalence (replacementInclusion A f)
  apply (weakEquivalences_over_iff Z _).mpr
  exact (weakEquivalence_iff A _).mpr (fibrationReplacement_quasiIso A f)

/-- 概要：選んだ左脚置換は slice で fibrant（Hovey §1.3）。
方針：恒等射が slice の終対象であり、そこへの射の底が置換の射影である。
規約：局所的な具体的 E モデル構造。
使われ方：引き戻しの右導来比較が同型となる点を供給する。 -/
lemma replacementOver_isFibrant {X Z : (operad A).Algebra} (f : X ⟶ Z) :
    let := modelCategory A
    IsFibrant (replacementOver A f) := by
  let := modelCategory A
  change IsFibrant (replacementOver A f)
  apply (isFibrant_iff_of_isTerminal ((Over.mkIdTerminal (X := Z)).from (replacementOver A f))
    (Over.mkIdTerminal (X := Z))).mpr
  rw [fibrations_over_iff, Over.mkIdTerminal_from_left]
  exact ⟨(fibrationReplacement A f).hp⟩

/-- 概要：E 代数の homotopy 引き戻しの具体的な対象（Hovey §1.3）。
方針：左脚を slice の fibrant 対象へ置き換えて通常の引き戻しを取る。
規約：右脚・基底の代数は既に fibrant、両脚は任意。
使われ方：E2a-4 の底で計算する homotopy 引き戻し。 -/
def homotopyPullback {X Y Z : (operad A).Algebra} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (operad A).Algebra :=
  (pullbackFunctor A g).obj (replacementOver A f)

/-- 概要：具体的な homotopy 引き戻しは底の複体で同じ引き戻しとなる（BM 命題 4.1）。
方針：忘却関手の極限創出から標準の引き戻し比較同型を使う。
規約：底で用いる左脚は実際の置換の射影であり、元の左脚との混同はしない。
使われ方：E2a-4 の底での計算と E2b の導来忘却。
-/
def homotopyPullbackCarrierIso {X Y Z : (operad A).Algebra}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    (homotopyPullback A f g).carrier ≅ pullback (fibrationReplacement A f).p.hom g.hom :=
  PreservesPullback.iso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)) _ _

end SerrePositivity.EInfinity.BarrattEccles
