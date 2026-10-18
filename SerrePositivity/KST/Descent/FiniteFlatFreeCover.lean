module

public import SerrePositivity.KST.Descent.FiniteFlatTrivialization
public import SerrePositivity.KST.Descent.AffineTensorSquare
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# 有限忠実平坦なアフィン射の有限自由チャート被覆

## 概要
有限自由な基本開自明化を実際のアフィン開被覆と Cartesian なテンソル積チャートへ移す。

## 方針
証明済みの有限自明化の元を選び、Mathlib の基本開被覆と指定テンソル積射影を使う。

## 規約
自由基底を持つのは実際の底変換代数。元の代数の大域的な自由性は要求しない。

## 使われ方
論文 補題 3.2 の有限平坦 transfer に対する Zariski 自明化と Čech の底変換。
原典の τ 位相の層論を Čech 計算へ置換する際の実際の有限被覆。
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
open scoped TensorProduct

namespace SerrePositivity.KST.Descent

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] [Module.Finite R B]
  [Module.Flat R B] [Module.FinitePresentation R B]
  [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B)))]

/-- 概要：正の有限自由自明化を与える有限個の元（論文 補題 3.2）。
方針：存在定理の有限部分族を選ぶ。
規約：選択の根拠は証明済みの局所自由性で、自由性の追加仮定ではない。
使われ方：実際の基本開被覆の添字。 -/
noncomputable def finiteFlatFreeElements : Finset R :=
  (exists_positive_basis_tensor_cover R B).choose

/-- 概要：選んだ元は単位イデアルを生成する（論文 補題 3.2）。
方針：有限自明化の存在定理の被覆条件を取り出す。
規約：被覆は元の基礎環の Spec 全体。
使われ方：基本開の実際の開被覆の構成。 -/
theorem finiteFlatFreeElements_span :
    Ideal.span (finiteFlatFreeElements R B : Set R) = ⊤ :=
  (exists_positive_basis_tensor_cover R B).choose_spec.1

/-- 概要：選んだ各基本開の底変換代数は正の有限基底を持つ（論文 補題 3.2）。
方針：有限自明化の存在定理の基底条件を取り出す。
規約：基底は実際の局所化テンソル積に与える。
使われ方：局所 transfer の射影公式と rank の正規化。 -/
theorem finiteFlatFreeElements_basis (r : finiteFlatFreeElements R B) :
    ∃ rank : ℕ, 0 < rank ∧ Nonempty
      (Basis (Fin rank) (Localization.Away r.val) (Localization.Away r.val ⊗[R] B)) :=
  (exists_positive_basis_tensor_cover R B).choose_spec.2 r.val r.property

/-- 概要：有限自由な自明化の実際のアフィン開被覆（論文 補題 3.2）。
方針：単位イデアルを生成する有限個の元に標準の基本開被覆を適用する。
規約：各チャートは Spec R[1/r]、射は実際の局所化写像の Spec。
使われ方：Zariski Čech 降下へ渡す具体的な有限被覆。 -/
noncomputable def finiteFlatFreeSpecCover : (Spec (.of R)).AffineOpenCover :=
  Scheme.affineOpenCoverOfSpanRangeEqTop (fun r : finiteFlatFreeElements R B ↦ r.val)
    (by
      have h : Set.range (fun r : finiteFlatFreeElements R B ↦ r.val) =
          (finiteFlatFreeElements R B : Set R) := by
        ext r
        constructor
        · rintro ⟨i, rfl⟩
          exact i.property
        · intro hr
          exact ⟨⟨r, hr⟩, rfl⟩
      rw [h]
      exact finiteFlatFreeElements_span R B)

/-- 概要：自明化被覆の実際の添字型は有限（論文 補題 3.2）。
方針：選んだ有限集合の subtype を使う。
規約：被覆を無限個の素点で添字付けしない。
使われ方：有限 Zariski 被覆の Čech 計算。 -/
instance : Finite (finiteFlatFreeSpecCover R B).I₀ :=
  inferInstanceAs (Finite (finiteFlatFreeElements R B))

/-- 概要：自由チャートのテンソル積の指定射影は元の有限射の実際の底変換（補題 3.2）。
方針：テンソル積の Spec の Cartesian 正方形を左右反転する。
規約：基底のチャート射は構成した開被覆の射そのもの。
使われ方：自由基底を実際の底変換被覆の構造代数の基底として使う。 -/
theorem finiteFlatFreeSpecChart_isPullback (r : (finiteFlatFreeSpecCover R B).I₀) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        B →ₐ[R] Localization.Away r.val ⊗[R] B).toRingHom))
      (Spec.map (CommRingCat.ofHom
        (algebraMap (Localization.Away r.val) (Localization.Away r.val ⊗[R] B))))
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      ((finiteFlatFreeSpecCover R B).f r) :=
  (tensorSpecSquare_isPullback R (Localization.Away r.val) B).flip

section BaseChange

variable {R B} {C A : Type u} [CommRing C] [CommRing A]
  [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
  {ι : Type v}

omit [Module.Finite R B] [Module.Flat R B] [Module.FinitePresentation R B]
  [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B)))] in
/-- 概要：チャートの実際の自由基底を任意の係数底変換へ同じ添字で移す（補題 3.2）。
方針：基底を底変換し、二重テンソル積の実際の標準同型で直接のテンソル積へ移す。
規約：追加の平坦性や非零性は不要。添字 Fin rank と正の rank を保つ。
使われ方：Čech 各段と係数拡大で同じ局所 rank 公式を使うための基底。 -/
noncomputable def tensorFreeBasisBaseChange (b : Basis ι C (C ⊗[R] B)) :
    Basis ι A (A ⊗[R] B) :=
  (b.baseChange A).map (TensorProduct.AlgebraTensorModule.cancelBaseChange R C A A B)

end BaseChange

end SerrePositivity.KST.Descent
