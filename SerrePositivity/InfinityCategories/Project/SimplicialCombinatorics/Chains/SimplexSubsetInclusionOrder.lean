module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Chains.SimplexSubsetOrder

/-! # 元の有限部分集合の包含の局所頂点作用
概要：元の部分集合の包含を、同じ昇順単体の局所頂点番号の間の単調写像にする。
方針：元の大きい部分集合の昇順列挙の逆で、元の小さい部分集合の頂点を読む。
規約：元の全頂点像を保持。使われ方：HA の内部点削除の実 necklace 射。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction

/-- 元の HA 添字部分集合は、同じ濃度条件から非空。 -/
lemma simplexSubsetNonempty {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    I.Nonempty := Finset.card_pos.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hI)

/-- 元の部分集合包含が誘導する、同じ二つの昇順列挙の局所番号間の単調写像。 -/
def simplexSubsetInclusionOrder {n : ℕ} (I J : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J) :
    Fin (I.card - 1 + 1) →o Fin (J.card - 1 + 1) where
  toFun v := (J.orderIsoOfFin (show J.card = J.card - 1 + 1 by omega)).symm
    ⟨_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI v, hIJ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_mem I hI v)⟩
  monotone' v w hvw :=
    (J.orderIsoOfFin (show J.card = J.card - 1 + 1 by omega)).symm.monotone
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI).monotone hvw)

/-- 元の局所番号の包含は、大きい昇順単体で同じ元の頂点像を回収する。 -/
lemma simplexSubsetInclusionOrder_recovery {n : ℕ} (I J : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J) (v : Fin (I.card - 1 + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder J hJ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder I J hI hJ hIJ v) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI v :=
  congrArg Subtype.val
    ((J.orderIsoOfFin (show J.card = J.card - 1 + 1 by omega)).apply_symm_apply _)

/-- 元の部分集合包含は、同じ局所頂点番号の間で単射。 -/
lemma simplexSubsetInclusionOrder_injective {n : ℕ} (I J : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder I J hI hJ hIJ) := by
  intro v w h
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_injective I hI
  exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder_recovery I J hI hJ hIJ v).symm.trans
    ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder J hJ) h).trans
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder_recovery I J hI hJ hIJ w))

/-- 元の包含と元の昇順列挙の合成は、小さい部分集合の元の列挙そのもの。 -/
lemma simplexSubsetInclusionOrder_triangle {n : ℕ} (I J : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder J hJ).comp (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder I J hI hJ hIJ) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI :=
  DFunLike.ext _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder_recovery I J hI hJ hIJ)

/-- 元の恒等包含は、同じ局所頂点番号の恒等写像。 -/
lemma simplexSubsetInclusionOrder_id {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder I I hI hI (fun _ h => h) = OrderHom.id := by
  apply DFunLike.ext
  intro v
  exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_injective I hI
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder_recovery I I hI hI (fun _ h => h) v)

/-- 元の包含の合成は、同じ局所番号の単調写像の合成を厳密に保つ。 -/
lemma simplexSubsetInclusionOrder_comp {n : ℕ} (I J K : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hK : 2 ≤ K.card) (hIJ : I ⊆ J) (hJK : J ⊆ K) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder I K hI hK (hIJ.trans hJK) =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder J K hJ hK hJK).comp
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder I J hI hJ hIJ) := by
  apply DFunLike.ext
  intro v
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_injective K hK
  exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder_recovery I K hI hK (hIJ.trans hJK) v).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder_recovery I J hI hJ hIJ v).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder_recovery J K hJ hK hJK _).symm)

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
