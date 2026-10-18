module

public import SerrePositivity.KST.DerivedBlowup.ExteriorProductDifferential

/-!
概要：KST Def3.1 の生成元追加の外積分解を同次次数へ制限する。
方針：収縮は次数を一つ下げ、射影・包含は次数を保つことを使う。
規約：第n+1外積を第n外積と第n+1外積の二成分へ分解する。
使われ方：反復 cone 模型との項ごとの比較同型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：生成元追加後の第n+1外積から shifted 成分を取り出す。
方針：最後の座標で収縮して第一因子へ射影する。
規約：KST Def3.1。使われ方：cone の一つ上の次数の成分。 -/
def exteriorProductDegreeTail (n : ℕ) :
    ExteriorAlgebra.exteriorPower R (n + 1) (M × R) →ₗ[R]
      ExteriorAlgebra.exteriorPower R n M :=
  (exteriorDegreeMap (LinearMap.fst R M R) n).comp
    (exteriorDegreeDifferential (LinearMap.snd R M R) n)

/-- 概要：同次な二成分から生成元追加後の同次外積を復元する。
方針：総外積の復元を制限し、最後の生成元との積の次数を検証する。
規約：KST Def3.1、第一成分は外積次数n。使われ方：次数別分解の逆写像。 -/
def exteriorProductDegreeJoin (n : ℕ) :
    (ExteriorAlgebra.exteriorPower R n M × ExteriorAlgebra.exteriorPower R (n + 1) M) →ₗ[R]
      ExteriorAlgebra.exteriorPower R (n + 1) (M × R) :=
  ((exteriorProductJoin (R := R) (M := M)).comp
    ((ExteriorAlgebra.exteriorPower R n M).subtype.prodMap
      (ExteriorAlgebra.exteriorPower R (n + 1) M).subtype)).codRestrict _ (by
        intro z
        change exteriorProductIn z.2.val + exteriorProductLast * exteriorProductIn z.1.val ∈ _
        apply Submodule.add_mem
        · exact exteriorMap_mem_degree (LinearMap.inl R M R) (n + 1) z.2.val z.2.property
        · have he : exteriorProductLast (R := R) (M := M) ∈
              ExteriorAlgebra.exteriorPower R 1 (M × R) := by
            simp only [ExteriorAlgebra.exteriorPower, pow_one]
            exact LinearMap.mem_range_self _ _
          have hx := exteriorMap_mem_degree (LinearMap.inl R M R) n z.1.val z.1.property
          simpa only [Nat.add_comm 1 n] using SetLike.mul_mem_graded he hx)

/-- 概要：生成元追加後の同次外積の二成分分解は線形同型。
方針：総外積で証明済みの分解と成分回収を部分加群へ制限する。
規約：KST Def3.1、第n+1外積の分解。使われ方：cone 比較の各次数の同型。 -/
def exteriorProductDegreeEquiv (n : ℕ) :
    ExteriorAlgebra.exteriorPower R (n + 1) (M × R) ≃ₗ[R]
      (ExteriorAlgebra.exteriorPower R n M × ExteriorAlgebra.exteriorPower R (n + 1) M) :=
  LinearEquiv.ofLinearMap
    ((exteriorProductDegreeTail n).prod (exteriorDegreeMap (LinearMap.fst R M R) (n + 1)))
    (exteriorProductDegreeJoin n) (by
      apply LinearMap.ext
      intro z
      apply Prod.ext
      · apply Subtype.ext
        exact exteriorProductTail_join z.1.val z.2.val
      · apply Subtype.ext
        exact exteriorProductOut_join z.1.val z.2.val) (by
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact (exteriorProduct_decomposition z.val).symm)

end SerrePositivity.KST.DerivedBlowup
