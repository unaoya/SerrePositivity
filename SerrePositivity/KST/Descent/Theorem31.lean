module

public import SerrePositivity.KST.Descent.SplitMayerVietoris
public import SerrePositivity.KST.Descent.EquivariantMayerVietoris
public import SerrePositivity.KST.Descent.PermutationRepresentation
public import SerrePositivity.KST.Descent.InvariantProducts
public import SerrePositivity.KST.Descent.OrbitDescentStep
public import SerrePositivity.KST.Descent.ClosedCoverDescent
public import SerrePositivity.KST.Descent.ComponentRemainderCover
public import SerrePositivity.KST.Descent.ClosedCoverIntersectionGeometry
public import SerrePositivity.KST.Descent.BasicDescent
public import SerrePositivity.KST.Descent.IntegralDescentStep
public import SerrePositivity.KST.Descent.SectionedDescent

/-!
# 定理 3.1 の軌道正方形における全次数の貼り合わせ

## 概要
(3.8) の置換不変部分と閉中心上の帰納仮定から、元の軌道比較の全次数同型を得る。
公開する `OrbitDescentStep` では、実際の同変軌道正方形とその二つのコピー分解を用い、
中心上の降下から指定された全次数 PiDescent を導く。
`ClosedCoverDescent` では、二つの閉部分と実際の交わりの指定降下から元の射の全次数降下を導く。
`ComponentRemainderCover` では、整な成分の有限被覆と交わりの次元低下を構成する。
交わりの指定比較の切断・推移性と、両側の被約化後の被覆、空の基底の降下も公開する。
整な基底では、低次元に限った帰納仮定から中心上の降下を導き、軌道段階を閉じる。
`SectionedDescent` では成分数と次元の帰納を完了し、切断を持つ場合の指定降下を証明する。
本ファイルの宣言は、これと併用する代数的な表現による貼り合わせを記述する。

## 方針
比較元の恒等的な正方形の分裂長完全列と比較する。
積の比較は対角写像と閉中心上の指定比較、交わりの比較は対角写像から構成する。

## 規約
定理 3.1 全体の完成版ではない。実際の L の降下から自然な長完全列と有限積保存を供給し、
幾何的推移性からの被覆はアフィンの場合と実際の閉中心へ接続済み。
切断を持つ場合の次元帰納は完了。切断を持たない射への Čech 還元と、実降下の条件の供給は残る。
主張の結論そのものを仮定していない。

## 使われ方
論文 定理 3.1 の証明で、軌道正方形の (3.8) と真閉中心上の帰納仮定を使う部分。
原典の τ 位相の層論を Čech 計算に置換する全体経路の一部。
-/

@[expose] public section

universe u

open CategoryTheory Representation

namespace SerrePositivity.KST.Descent

variable {G I : Type*} [Group G] [MulAction G I]

/-- 概要：軌道正方形の二つの部分への比較（論文 定理 3.1、(3.8)）。
方針：Y の元は定数族へ、Z の元は中心上の指定比較へ送り、積の分解を逆に辿る。
規約：分解はコピーへの制限と固定部分の積に対応するものとして別途供給する。
使われ方：軌道正方形の長完全列の B 成分の指定比較。 -/
noncomputable def orbitProductComparison {Y Z U B : Type*}
    [AddCommGroup Y] [Module ℚ Y] [AddCommGroup Z] [Module ℚ Z]
    [AddCommGroup U] [Module ℚ U] [AddCommGroup B] [Module ℚ B]
    (ρU : Representation ℚ G U)
    (decomposition : B ≃ₗ[ℚ] (permutationRepresentation G I Y).invariants × ρU.invariants)
    (center : Z →ₗ[ℚ] ρU.invariants) : Y × Z →ₗ[ℚ] B :=
  decomposition.symm.toLinearMap.comp ((permutationDiagonal G I Y).prodMap center)

/-- 概要：軌道正方形の交わりへの比較（論文 (3.8)）。
方針：中心上の値をコピー上の定数族へ送り、交わりの分解を逆に辿る。
規約：分解はコピーへの制限に対応するものとして別途供給する。
使われ方：軌道正方形の長完全列の C 成分の指定比較。 -/
noncomputable def orbitIntersectionComparison {Z C : Type*}
    [AddCommGroup Z] [Module ℚ Z] [AddCommGroup C] [Module ℚ C]
    (decomposition : C ≃ₗ[ℚ] (permutationRepresentation G I Z).invariants) : Z →ₗ[ℚ] C :=
  decomposition.symm.toLinearMap.comp (permutationDiagonal G I Z)

/-- 概要：(3.8) と閉中心上の帰納仮定から元の指定軌道比較が全次数同型（定理 3.1）。
方針：対角比較の全単射性、積の比較、分裂長完全列の五項補題を組み合わせる。
規約：T は実際の固定部分の長完全列として別途供給する。
境界の可換性を追加仮定にせず、比較元の差の全射性から証明する。
使われ方：整な基底上での軌道正方形の帰納段階。全体の Čech 還元と幾何構成は未接続。 -/
theorem orbitStep_pi_bijective [MulAction.IsPretransitive G I] [Nonempty I]
    (Y Z U : ℤ → ModuleCat.{u} ℚ) (r : ∀ n, Y n →ₗ[ℚ] Z n)
    (T : GradedMayerVietoris.{u}) (ρU : ∀ n, Representation ℚ G (U n))
    (decompositionB : ∀ n, T.B n ≃ₗ[ℚ]
      (permutationRepresentation G I (Y n)).invariants × (ρU n).invariants)
    (decompositionC : ∀ n, T.C n ≃ₗ[ℚ] (permutationRepresentation G I (Z n)).invariants)
    (center : ∀ n, Z n →ₗ[ℚ] (ρU n).invariants)
    (center_bijective : ∀ n, Function.Bijective (center n))
    (comparison : ∀ n, Y n →ₗ[ℚ] T.A n)
    (restriction_naturality : ∀ n, (T.restriction n).comp (comparison n) =
      (orbitProductComparison (ρU n) (decompositionB n) (center n)).comp (splitRestriction (r n)))
    (difference_naturality : ∀ n, (T.difference n).comp
      (orbitProductComparison (ρU n) (decompositionB n) (center n)) =
      (orbitIntersectionComparison (decompositionC n)).comp (splitDifference (r n)))
    (n : ℤ) : Function.Bijective (comparison n) := by
  apply splitMayerVietorisComparison_bijective Y Z r T comparison
    (fun k ↦ orbitProductComparison (ρU k) (decompositionB k) (center k))
    (fun k ↦ orbitIntersectionComparison (decompositionC k))
    restriction_naturality difference_naturality ?_ ?_ n
  · intro k
    have product_bijective : Function.Bijective
        ((permutationDiagonal G I (Y k)).prodMap (center k)) :=
      (LinearEquiv.prodCongr
        (LinearEquiv.ofBijective (permutationDiagonal G I (Y k))
          (permutationDiagonal_bijective G I (Y k)))
        (LinearEquiv.ofBijective (center k) (center_bijective k))).bijective
    exact (decompositionB k).symm.bijective.comp product_bijective
  · intro k
    exact (decompositionC k).symm.bijective.comp (permutationDiagonal_bijective G I (Z k))

end SerrePositivity.KST.Descent
