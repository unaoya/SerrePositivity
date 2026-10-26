module
public import SerrePositivity.KST.SConstruction.Cofinality.CokernelIntervals
public import SerrePositivity.KST.Spectra.GroupNerveCoordinates

/-!
概要：元の S 余核の各元を同じ余核群の nerve の単体にする。
方針：全区間の値を射とし、区間の加法関係を関手の合成則へ移す。
規約：元の全端点制限を保ち、自由な bar の同定を仮定しない。
使われ方：元の障害図式から群 nerve への比較射。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の S_n 余核の全区間値を群 nerve の n 単体に束ねる。
方針：区間値の自己零性と加法性から一対象群圏への関手を作る。
規約：SingleObj の合成順序は逆順なので、元の可換群の交換則を明示する。
使われ方：元の障害図式の bar 比較の次数ごとの射。 -/
def cutCokernelNerveSimplex {X Y : StableModel.{u}} (f : X ⟶ Y)
    (n : ℕ) (a : cutKZeroCokernel n f) :
    (nerve (AsSmall.{u} (SingleObj (Multiplicative (cutKZeroCokernel 1 f))))) _⦋n⦌ where
  obj _ := Spectra.GroupOverCodiscrete.star (Multiplicative (cutKZeroCokernel 1 f))
  map {i j} α := ULift.up (Multiplicative.ofAdd
    (cutCokernelRestriction f (cokernelIntervalOrder i j (leOfHom α)) a))
  map_id i := by
    apply ULift.ext
    exact congrArg Multiplicative.ofAdd (cutCokernel_interval_self f a i)
  map_comp {i j k} α β := by
    apply ULift.ext
    exact congrArg Multiplicative.ofAdd
      ((cutCokernel_interval_add f a i j k (leOfHom α) (leOfHom β)).trans (add_comm _ _))

end SerrePositivity.KST.SConstruction.Cofinality
