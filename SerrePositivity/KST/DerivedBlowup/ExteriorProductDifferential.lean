module

public import SerrePositivity.KST.DerivedBlowup.ExteriorProductEquiv

/-!
概要：KST Def3.1 の生成元追加による外積分解と Koszul 微分の比較。
方針：追加生成元 e の微分を a として収縮の積公式を計算する。
規約：二成分は shifted 成分、元の成分の順。微分行列は (-d,0;a,d)。
使われ方：既存反復 cone の微分との比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：最後の生成元の微分を a とする生成元追加後の微分。
方針：第一因子の微分と最後の座標の a 倍を足す。
規約：KST Def3.1。使われ方：反復 cone に対応する外積微分。 -/
def exteriorProductDifferential (d : M →ₗ[R] R) (a : R) : (M × R) →ₗ[R] R :=
  d.comp (LinearMap.fst R M R) + a • LinearMap.snd R M R

/-- 概要：生成元追加後の微分は第一因子で元の微分になる。
方針：座標射影と包含を評価する。
規約：KST Def3.1。使われ方：外積包含と収縮の自然性。 -/
theorem exteriorProductDifferential_in (d : M →ₗ[R] R) (a : R) :
    (exteriorProductDifferential d a).comp (LinearMap.inl R M R) = d := by
  ext m
  simp [exteriorProductDifferential]

/-- 概要：外積二成分分解上の Koszul 微分は cone の行列になる。
方針：第一因子上の自然性と最後の生成元の Leibniz 公式を使う。
規約：KST Def3.1、微分は (x,y)↦(-dx,ax+dy)。使われ方：cone 比較の chain 条件。 -/
theorem exteriorProduct_contract_join (d : M →ₗ[R] R) (a : R)
    (x y : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft (Q := 0) (exteriorProductDifferential d a)
        (exteriorProductJoin (x, y)) =
      exteriorProductJoin
        (-CliffordAlgebra.contractLeft (Q := 0) d x,
          a • x + CliffordAlgebra.contractLeft (Q := 0) d y) := by
  have hin (z : ExteriorAlgebra R M) := exteriorContraction_map (LinearMap.inl R M R)
    d (exteriorProductDifferential d a) (exteriorProductDifferential_in d a) z
  have he : exteriorProductDifferential d a (0, 1) = a := by
    simp [exteriorProductDifferential]
  change CliffordAlgebra.contractLeft (Q := 0) (exteriorProductDifferential d a)
      (exteriorProductIn y + ExteriorAlgebra.ι R (0, (1 : R)) * exteriorProductIn x) =
    exteriorProductIn (a • x + CliffordAlgebra.contractLeft (Q := 0) d y) +
      ExteriorAlgebra.ι R (0, (1 : R)) *
        exteriorProductIn (-CliffordAlgebra.contractLeft (Q := 0) d x)
  simp only [map_add, CliffordAlgebra.contractLeft_ι_mul, he, hin,
    map_neg, map_smul, mul_neg]
  abel

/-- 概要：任意の外積の微分を cone 型の二成分から復元する。
方針：総外積分解に contraction を適用して前の微分公式を使う。
規約：KST Def3.1。使われ方：二成分射影の微分適合性。 -/
theorem exteriorProduct_contract_decomposition (d : M →ₗ[R] R) (a : R)
    (z : ExteriorAlgebra R (M × R)) :
    CliffordAlgebra.contractLeft (Q := 0) (exteriorProductDifferential d a) z =
      exteriorProductJoin
        (-CliffordAlgebra.contractLeft (Q := 0) d (exteriorProductTail z),
          a • exteriorProductTail z +
            CliffordAlgebra.contractLeft (Q := 0) d (exteriorProductOut z)) := by
  calc
    _ = CliffordAlgebra.contractLeft (Q := 0) (exteriorProductDifferential d a)
        (exteriorProductJoin (exteriorProductTail z, exteriorProductOut z)) :=
      congrArg _ (exteriorProduct_decomposition z)
    _ = _ := exteriorProduct_contract_join d a _ _

end SerrePositivity.KST.DerivedBlowup
