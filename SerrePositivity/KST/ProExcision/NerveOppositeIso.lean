module
public import SerrePositivity.KST.ProExcision.NerveOppositeMap

/-!
# 反対圏の nerve と単体の順序反転の自然な実同型

概要：反対圏の nerve を元の nerve の順序反転と実同型で同定する。
方針：可合成射の列の反転の実逆写像を用いる。
規約：KST Proposition 4.14、SW92 §1.2 の反対 bar の実比較。
使われ方：係数方向の rev と合わせた対角 bar の行側比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
variable (C : Type u) [Category.{v} C]

/-- 概要：反対圏の列と元の圏の列の反転による実全単射。
方針：二回の反転が恒等となる二つの実写像を使う。
規約：SW92 §1.2。使われ方：反対 nerve の各次数の実同型。 -/
def oppositeNerveSimplexEquiv (n : ℕ) : ComposableArrows Cᵒᵖ n ≃ ComposableArrows C n where
  toFun := oppositeNerveSimplex
  invFun := nerveOppositeSimplex
  left_inv := nerveOppositeSimplex_oppositeNerveSimplex
  right_inv := oppositeNerveSimplex_nerveOppositeSimplex

/-- 概要：反対圏の nerve と元の nerve の順序反転の実単体的同型。
方針：各次数の実全単射を、証明済みの実単体写像の自然性で束ねる。
規約：KST Proposition 4.14、SW92 §1.2。実現の同定を仮定しない。
使われ方：反対モノイドの対角 bar の比較。 -/
def nerveOppositeIso : nerve Cᵒᵖ ≅ (nerve C).op :=
  NatIso.ofComponents
    (fun k ↦ Equiv.toIso ((oppositeNerveSimplexEquiv C k.unop.len).trans (SSet.opObjEquiv (X := nerve C) (n := k)).symm))
    (fun φ ↦ (nerveOppositeMap C).naturality φ)

/-- 概要：反対 nerve の実同型は圏の実関手に自然。
方針：反転した列を関手で送る二つの順序を定義で評価する。
規約：SW92 §1.2、係数方向の自然性。
使われ方：二重単体的 bar の対角への制限。 -/
lemma nerveOppositeIso_natural {D : Type u} [Category.{v} D] (f : C ⥤ D) :
    nerveMap f.op ≫ (nerveOppositeIso D).hom =
      (nerveOppositeIso C).hom ≫ SSet.opFunctor.map (nerveMap f) := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro F
  rfl

end SerrePositivity.KST.ProExcision
