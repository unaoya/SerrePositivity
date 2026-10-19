module
public import SerrePositivity.KST.ProExcision.SingleObjOppositeNerve

/-!
# 係数反転した反対モノイドの対角 bar の実比較

概要：係数方向の rev と反対モノイドを施した bar を、対角全体の op と同定する。
方針：各 nerve の反転の実同型を二重単体的図式に束ねて対角に制限する。
規約：KST Proposition 4.14、SW92 §1.2。二つの単体方向の反転を両方含める。
使われ方：行側への相対ホモロジーの零化の移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open Comparison

/-- 概要：係数反転した反対モノイドの二重 bar と両方向の反転の実同型。
方針：実反対 nerve 同型を各係数次数に適用し、係数準同型への自然性を使う。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：実対角同型の構成。 -/
def bisimplicialBarReverseOppositeIso (M : SimplicialObject MonCat.{u}) :
    bisimplicialBar (monoidReverseOpposite M) ≅
      (SimplicialObject.opFunctor.obj (bisimplicialBar M)) ⋙ SSet.opFunctor :=
  NatIso.ofComponents (fun k ↦ monoidOppositeNerveIso (M.obj k)) (by
    intro k l f
    exact monoidOppositeNerveIso_natural
      (M.map (SimplexCategory.rev.map f.unop).op).hom)

/-- 概要：反転した反対モノイドの対角 bar と元の対角 bar の op の実同型。
方針：二重図式の実同型を uncurry して対角に前合成する。
規約：KST Proposition 4.14、SW92 §1.2。実現やホモロジー不変性を仮定しない。
使われ方：証明済みの符号付き鎖反転と行側比較の接続。 -/
def monoidBarReverseOppositeIso (M : SimplicialObject MonCat.{u}) :
    monoidBar (monoidReverseOpposite M) ≅ (monoidBar M).op :=
  Functor.isoWhiskerLeft (Functor.diag SimplexCategoryᵒᵖ)
    (Functor.uncurry.mapIso (bisimplicialBarReverseOppositeIso M))

/-- 概要：対角 bar の反転同型は単体的モノイドの実射に自然。
方針：各次数で射の列を送る操作と反転の順序を直接比較する。
規約：KST Proposition 4.14、SW92 §1.2。
使われ方：行側の相対対射と係数右乗法への移送。 -/
lemma monoidBarReverseOppositeIso_natural {M N : SimplicialObject MonCat.{u}}
    (f : M ⟶ N) :
    monoidBarMap (monoidReverseOppositeMap f) ≫ (monoidBarReverseOppositeIso N).hom =
      (monoidBarReverseOppositeIso M).hom ≫ SSet.opFunctor.map (monoidBarMap f) := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro F
  rfl

end SerrePositivity.KST.ProExcision
