module
public import SerrePositivity.KST.ProExcision.SimplicialReversalComponents
public import SerrePositivity.KST.Comparison.PiZeroRing

/-!
# 単体的環の順序反転と成分環

概要：係数方向を反転した単体的環の成分環を元の成分環と実環同型で比較する。
方針：同じ零次の代表を保つ連結成分の実全単射に加法・乗法保存を付ける。
規約：KST Proposition 4.14、非可換な行側の ĜL の成分での可逆性の比較。
使われ方：係数の rev と転置を伴う実行列の移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite SSet
open scoped Simplicial

/-- 概要：順序反転した単体的環の成分環と元の成分環の実環同型。
方針：零次の代表上で成分の実全単射の加法・乗法保存を証明する。
規約：KST Proposition 4.14、非可換な積の順を変えない。
使われ方：反転した係数図式の ĜL の単位条件。 -/
def ringReversalComponentsEquiv (A : SimplicialObject RingCat.{u}) :
    π₀ (Comparison.ringSpace (SimplicialObject.opFunctor.obj A)) ≃+* π₀ (Comparison.ringSpace A) where
  toEquiv := reversalComponentsEquiv (Comparison.ringSpace A)
  map_add' x y := by
    induction x using π₀.rec with | mk x => ?_
    induction y using π₀.rec with | mk y => ?_
    rfl
  map_mul' x y := by
    induction x using π₀.rec with | mk x => ?_
    induction y using π₀.rec with | mk y => ?_
    rfl

/-- 概要：成分環の反転比較は同じ零次の代表を保つ。
方針：連結成分の商写像で定義を評価する。
規約：KST Proposition 4.14。使われ方：実成分行列の比較。 -/
lemma ringReversalComponentsEquiv_mk (A : SimplicialObject RingCat.{u}) (x : A.obj (op ⦋0⦌)) :
    ringReversalComponentsEquiv A
      (π₀.mk ((SimplicialObject.opObjIso (X := A) (n := op ⦋0⦌)).inv x)) = π₀.mk x := rfl

/-- 概要：成分環の反転比較は任意の次数の成分写像と可換。
方針：反転は最初と最後の頂点を入れ替え、全ての頂点は同じ成分を表すことを使う。
規約：KST Proposition 4.14。使われ方：反転した ĜL の成分行列の単位条件。 -/
lemma ringReversalComponentsEquiv_simplex (A : SimplicialObject RingCat.{u}) (n : ℕ)
    (x : A.obj (op ⦋n⦌)) :
    ringReversalComponentsEquiv A
      (Comparison.SimplicialRing.simplexToComponents (SimplicialObject.opFunctor.obj A) n
        ((SimplicialObject.opObjIso (X := A) (n := op ⦋n⦌)).inv x)) =
      Comparison.SimplicialRing.simplexToComponents A n x := by
  have hc : SimplexCategory.rev.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) =
      SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    change (0 : Fin (n + 1)).rev = Fin.last n
    simp
  change π₀.mk (X := Comparison.ringSpace A) (A.map (SimplexCategory.rev.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)).op x) =
    π₀.mk (X := Comparison.ringSpace A) (A.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op x)
  rw [hc]
  exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexVertex_class_eq (Comparison.ringSpace A) x (Fin.last n)).symm

end SerrePositivity.KST.ProExcision
