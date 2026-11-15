module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutComposition
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionWholeInterval

/-!
概要：両外端の間の切れ目から左右の実因子を構成し、切れ目と分解の往復を証明する。
方針：実区間関手の水平合成則を全区間の回収につなぐ。
規約：分解の存在や合成の等式を仮定しない。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の切れ目による実分解。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {n : ℕ} {X Y M : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

/-- 概要：同種の切れ目は全頂点の自然数の座標で区別できる。
方針：二種類の有限点の外延性に戻す。規約：自然性の条件も保持する。
使われ方：Riehl–Verity §4.1の切れ目の往復。 -/
lemma walkingAdjunctionCut_ext {a b : WalkingAdjunctionCut H M}
    (h : ∀ i, walkingAdjunctionCutCoordinate a i = walkingAdjunctionCutCoordinate b i) : a = b := by
  cases M
  · apply WalkingAdjunctionPlusCut.ext
    intro i
    exact Fin.ext (h i)
  · apply WalkingAdjunctionMinusCut.ext
    intro i
    exact Fin.ext (h i)

/-- 概要：両外端の間にある切れ目から元の全単体の実水平分解を作る。
方針：両側の実区間関手を作り、合成則と全区間の回収で検収する。
規約：全関手と全射の合成の等式を構成する。使われ方：Riehl–Verity §4.1。 -/
def walkingAdjunctionFactorizationOfCut (a : WalkingAdjunctionCut H M)
    (hl : ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
      walkingAdjunctionCutRank a i)
    (hr : ∀ i, walkingAdjunctionCutRank a i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i) :
    WalkingAdjunctionFactorization H where
  middle := M
  left := walkingAdjunctionCutIntervalFunctor (walkingAdjunctionSourceCut H) a hl
  right := walkingAdjunctionCutIntervalFunctor a (walkingAdjunctionTargetCut H) hr
  fac := (walkingAdjunctionCutIntervalFunctor_comp (walkingAdjunctionSourceCut H) a
    (walkingAdjunctionTargetCut H) hl hr).trans (walkingAdjunctionWholeInterval H)

/-- 概要：構成した実分解の切れ目の座標は元の切れ目の座標。
方針：左因子の重みは左端0からの座標差。規約：全頂点。
使われ方：Riehl–Verity §4.1の切れ目の回収。 -/
lemma walkingAdjunctionFactorizationOfCut_coordinate (a : WalkingAdjunctionCut H M)
    (hl : ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
      walkingAdjunctionCutRank a i)
    (hr : ∀ i, walkingAdjunctionCutRank a i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i) (i : Fin (n + 1)) :
    walkingAdjunctionCutCoordinate (walkingAdjunctionFactorizationOfCut a hl hr).cut i =
      walkingAdjunctionCutCoordinate a i := by
  rw [WalkingAdjunctionFactorization.cut_coordinate]
  change walkingAdjunctionWeight X M
    (walkingAdjunctionCutIntervalObject (walkingAdjunctionSourceCut H) a hl i) = _
  rw [walkingAdjunctionCutIntervalObject_weight, walkingAdjunctionSourceCut_coordinate,
    Nat.sub_zero]

/-- 概要：切れ目から実分解を作って戻すと同じ切れ目。
方針：全頂点の座標の一致を使う。規約：自然性も含む実データの等式。
使われ方：Riehl–Verity §4.1の切れ目と分解の往復。 -/
lemma walkingAdjunctionFactorizationOfCut_cut (a : WalkingAdjunctionCut H M)
    (hl : ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
      walkingAdjunctionCutRank a i)
    (hr : ∀ i, walkingAdjunctionCutRank a i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i) :
    (walkingAdjunctionFactorizationOfCut a hl hr).cut = a :=
  walkingAdjunctionCut_ext (walkingAdjunctionFactorizationOfCut_coordinate a hl hr)

/-- 概要：実分解の切れ目から作った実分解は元の分解。
方針：切れ目の回収と左因子の長さによる実分解の一意性を使う。
規約：左右の全関手と合成の証明を含む等式。使われ方：Riehl–Verity §4.1。 -/
lemma WalkingAdjunctionFactorization.ofCut_roundtrip (a : WalkingAdjunctionFactorization H) :
    walkingAdjunctionFactorizationOfCut a.cut a.sourceCut_le a.le_targetCut = a := by
  let b := walkingAdjunctionFactorizationOfCut a.cut a.sourceCut_le a.le_targetCut
  apply b.ext_prefix_length a
  intro i
  have hb := b.cut_rank i
  have ha := a.cut_rank i
  have hc := congrArg (fun c : WalkingAdjunctionCut H a.middle => walkingAdjunctionCutRank c i)
    (walkingAdjunctionFactorizationOfCut_cut a.cut a.sourceCut_le a.le_targetCut)
  change walkingAdjunctionCutRank b.cut i = walkingAdjunctionCutRank a.cut i at hc
  omega

end SerrePositivity.InfinityCategories.HA.Monads
