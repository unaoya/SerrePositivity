module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionResidualFunctor
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionUnits

/-!
概要：全単体の左右の単位分解から外端の切れ目を取り出す。
方針：実単位則で分解を作り、既存の切れ目の座標・順位の照合を適用する。
規約：分解の端点も元の実Homの対象である。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の区間の境界。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {n : ℕ} {X Y : WalkingAdjunctionPoint}

/-- 概要：全単体の左端の実分解。
方針：左の定値単位関手と元の全単体を合成する。規約：左単位則で検収する。
使われ方：Riehl–Verity §4.1の左端の切れ目。 -/
def walkingAdjunctionSourceFactorization (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionFactorization H where
  middle := X
  left := (Functor.const _).obj (walkingAdjunctionIdentity X)
  right := H
  fac := walkingAdjunctionHorizontal_leftUnit X Y H

/-- 概要：全単体の右端の実分解。
方針：元の全単体と右の定値単位関手を合成する。規約：右単位則で検収する。
使われ方：Riehl–Verity §4.1の右端の切れ目。 -/
def walkingAdjunctionTargetFactorization (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionFactorization H where
  middle := Y
  left := H
  right := (Functor.const _).obj (walkingAdjunctionIdentity Y)
  fac := walkingAdjunctionHorizontal_rightUnit X Y H

/-- 概要：全単体の始点に対応する実切れ目。
方針：左単位分解から取る。規約：同じH上の切れ目。
使われ方：Riehl–Verity §4.1の区間の左端。 -/
def walkingAdjunctionSourceCut (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionCut H X := (walkingAdjunctionSourceFactorization H).cut

/-- 概要：全単体の終点に対応する実切れ目。
方針：右単位分解から取る。規約：同じH上の切れ目。
使われ方：Riehl–Verity §4.1の区間の右端。 -/
def walkingAdjunctionTargetCut (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionCut H Y := (walkingAdjunctionTargetFactorization H).cut

/-- 概要：左端の切れ目の座標は0。
方針：単位の重みを使う。規約：全頂点。
使われ方：Riehl–Verity §4.1の元の全単体の回収。 -/
lemma walkingAdjunctionSourceCut_coordinate
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (i : Fin (n + 1)) :
    walkingAdjunctionCutCoordinate (walkingAdjunctionSourceCut H) i = 0 := by
  exact ((walkingAdjunctionSourceFactorization H).cut_coordinate i).trans
    (walkingAdjunctionIdentity_weight X)

/-- 概要：右端の切れ目の座標は元の全単体の重み。
方針：右単位分解の左因子はH自身。規約：全頂点。
使われ方：Riehl–Verity §4.1の元の全単体の回収。 -/
lemma walkingAdjunctionTargetCut_coordinate
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (i : Fin (n + 1)) :
    walkingAdjunctionCutCoordinate (walkingAdjunctionTargetCut H) i =
      walkingAdjunctionWeight X Y (H.obj i) :=
  (walkingAdjunctionTargetFactorization H).cut_coordinate i

/-- 概要：左端の順位は始点の補正。
方針：単位の長さ0を使う。規約：全頂点。
使われ方：Riehl–Verity §4.1の許される切れ目の下限。 -/
lemma walkingAdjunctionSourceCut_rank
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (i : Fin (n + 1)) :
    walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i =
      walkingAdjunctionTargetCorrection X := by
  rw [walkingAdjunctionCutRank, walkingAdjunctionSourceCut_coordinate]
  omega

/-- 概要：右端の順位は全単体の長さと始点の補正の和。
方針：分解の順位の法則を適用する。規約：全頂点。
使われ方：Riehl–Verity §4.1の許される切れ目の上限。 -/
lemma walkingAdjunctionTargetCut_rank
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (i : Fin (n + 1)) :
    walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i =
      walkingAdjunctionVertexLength X Y (H.obj i) + walkingAdjunctionTargetCorrection X :=
  (walkingAdjunctionTargetFactorization H).cut_rank i

/-- 概要：左端の切れ目は右端以下。
方針：元の全単体の長さの非負性を使う。規約：全頂点で比較する。
使われ方：Riehl–Verity §4.1の全区間の実関手。 -/
lemma walkingAdjunctionOuterCuts_le
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i := by
  intro i
  rw [walkingAdjunctionSourceCut_rank, walkingAdjunctionTargetCut_rank]
  omega

/-- 概要：任意の実分解の切れ目は左端以上。
方針：左因子の長さの非負性を使う。規約：実分解から来る切れ目。
使われ方：Riehl–Verity §4.1の区間の回収。 -/
lemma WalkingAdjunctionFactorization.sourceCut_le
    {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y} (a : WalkingAdjunctionFactorization H) :
    ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
      walkingAdjunctionCutRank a.cut i := by
  intro i
  rw [walkingAdjunctionSourceCut_rank, a.cut_rank]
  omega

/-- 概要：任意の実分解の切れ目は右端以下。
方針：全水平合成の長さの加法則を使う。規約：実分解から来る切れ目。
使われ方：Riehl–Verity §4.1の区間の回収。 -/
lemma WalkingAdjunctionFactorization.le_targetCut
    {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y} (a : WalkingAdjunctionFactorization H) :
    ∀ i, walkingAdjunctionCutRank a.cut i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i := by
  intro i
  rw [a.cut_rank, walkingAdjunctionTargetCut_rank]
  have he := congrArg (fun F => F.obj i) a.fac
  have hl := walkingAdjunctionVertexLength_comp X a.middle Y (a.left.obj i) (a.right.obj i)
  change (walkingAdjunctionHorizontal X a.middle Y).obj (a.left.obj i, a.right.obj i) =
    H.obj i at he
  rw [he] at hl
  omega

end SerrePositivity.InfinityCategories.HA.Monads
