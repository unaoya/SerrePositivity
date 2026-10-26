module
public import SerrePositivity.KST.SConstruction.Cofinality.CutKZeroConstant

/-!
概要：元の左右の区間制限による三角圏 K₀ の直積分解。
方針：元の切断 cofiber 関係と区間の収縮の二つの逆律を使う。
規約：実現比較や共終性を仮定しない。
使われ方：全 S 多次数の障害余核の bar 同定。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 概要：左の延長後の左制限は K₀ で恒等。
方針：短い区間の包含と収縮の厳密な逆律を使う。
規約：元の端点制限の合成。
使われ方：区間分解の右逆。 -/
lemma cutKZero_left_recover (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    (cutKZeroRestriction X (cutLeftIntervalInclusion n k)).comp
      (cutKZeroRestriction X (cutLeftIntervalRetraction n k)) = AddMonoidHom.id _ :=
  (cutKZeroRestriction_comp X _ _).symm.trans
    ((congrArg (cutKZeroRestriction X) (cutLeftInterval_retraction_inclusion n k)).trans
      (cutKZeroRestriction_id _ X))

/-- 概要：右の延長後の右制限は K₀ で恒等。
方針：短い区間の包含と収縮の厳密な逆律を使う。
規約：元の端点制限の合成。
使われ方：区間分解の右逆。 -/
lemma cutKZero_right_recover (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    (cutKZeroRestriction X (cutRightIntervalInclusion n k)).comp
      (cutKZeroRestriction X (cutRightIntervalRetraction n k)) = AddMonoidHom.id _ :=
  (cutKZeroRestriction_comp X _ _).symm.trans
    ((congrArg (cutKZeroRestriction X) (cutRightInterval_retraction_inclusion n k)).trans
      (cutKZeroRestriction_id _ X))

/-- 概要：右延長を左区間に制限すると K₀ で零。
方針：端点写像の合成が定値零であることを計算する。
規約：境界の切断も含む。
使われ方：区間分解の交差項の消去。 -/
lemma cutKZero_left_cross (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    (cutKZeroRestriction X (cutLeftIntervalInclusion n k)).comp
      (cutKZeroRestriction X (cutRightIntervalRetraction n k)) = 0 := by
  have he : (cutRightIntervalRetraction n k).comp (cutLeftIntervalInclusion n k) =
      OrderHom.const (Fin (k.val + 1)) (0 : Fin (n - k.val + 1)) := by
    apply DFunLike.ext
    intro i
    apply Fin.ext
    change i.val - k.val = 0
    exact Nat.sub_eq_zero_of_le (Nat.le_of_lt_succ i.isLt)
  exact (cutKZeroRestriction_comp X _ _).symm.trans
    ((congrArg (cutKZeroRestriction X) he).trans (cutKZeroRestriction_constant X _))

/-- 概要：左延長を右区間に制限すると K₀ で零。
方針：端点写像の合成が左の終点で定値であることを計算する。
規約：境界の切断も含む。
使われ方：区間分解の交差項の消去。 -/
lemma cutKZero_right_cross (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    (cutKZeroRestriction X (cutRightIntervalInclusion n k)).comp
      (cutKZeroRestriction X (cutLeftIntervalRetraction n k)) = 0 := by
  have he : (cutLeftIntervalRetraction n k).comp (cutRightIntervalInclusion n k) =
      OrderHom.const (Fin (n - k.val + 1)) (Fin.last k.val) := by
    apply DFunLike.ext
    intro i
    apply Fin.ext
    change min (i.val + k.val) k.val = k.val
    exact min_eq_right (Nat.le_add_left _ _)
  exact (cutKZeroRestriction_comp X _ _).symm.trans
    ((congrArg (cutKZeroRestriction X) he).trans (cutKZeroRestriction_constant X _))

/-- 概要：元の左右の短い区間制限による K₀ の直積同型。
方針：逆写像は左右を元の区間に延長して足し、切断加法性で逆律を示す。
規約：同型の順射は元の二つの区間制限そのもの。
使われ方：相対障害群を全単体的な bar 群として読む。 -/
def cutKZeroEquiv (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    TriangulatedK0 (hoFunctor.obj (sStableModel n X).carrier) ≃+
      TriangulatedK0 (hoFunctor.obj (sStableModel k.val X).carrier) ×
        TriangulatedK0 (hoFunctor.obj (sStableModel (n - k.val) X).carrier) where
  toFun a := (cutKZeroRestriction X (cutLeftIntervalInclusion n k) a,
    cutKZeroRestriction X (cutRightIntervalInclusion n k) a)
  invFun a := cutKZeroRestriction X (cutLeftIntervalRetraction n k) a.1 +
    cutKZeroRestriction X (cutRightIntervalRetraction n k) a.2
  left_inv a := (DFunLike.congr_fun (cutKZero_interval_decomposition n k X) a).symm
  right_inv a := by
    apply Prod.ext
    · exact (map_add _ _ _).trans ((congrArg₂ (· + ·)
        (DFunLike.congr_fun (cutKZero_left_recover n k X) a.1)
        (DFunLike.congr_fun (cutKZero_left_cross n k X) a.2)).trans (add_zero _))
    · exact (map_add _ _ _).trans ((congrArg₂ (· + ·)
        (DFunLike.congr_fun (cutKZero_right_cross n k X) a.1)
        (DFunLike.congr_fun (cutKZero_right_recover n k X) a.2)).trans (zero_add _))
  map_add' a b := Prod.ext (map_add _ a b) (map_add _ a b)

end SerrePositivity.KST.SConstruction.Cofinality
