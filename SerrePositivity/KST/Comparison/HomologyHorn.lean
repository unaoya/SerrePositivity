module

public import SerrePositivity.KST.Comparison.HomologyPairContraction

/-!
# horn 包含の整数ホモロジー同型

概要：正次元の全ての horn 包含は整数ホモロジー同型を誘導する。
方針：min(x,k) を経由する二段階の実際の収縮を、部分単体集合のホモロジー比較へ適用する。
規約：Waldhausen LNM 1126 §1.7・§1.8 の Kan 置換のホモロジー計算の準備。
使われ方：horn 添付と anodyne map のホモロジー保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory
open scoped Simplicial

/--
概要：正次元の horn と標準単体の整数ホモロジーの同型。
方針：頂点への二段階収縮を部分単体集合上へ制限する。
規約：順方向の射は horn 包含が誘導する射である。
使われ方：horn 添付のホモロジー保存の生成射の計算。
-/
def hornIntegralHomologyIso {d : ℕ} [NeZero d] (k : Fin (d + 1)) (n : ℕ) :
    integralHomology (Λ[d, k] : SSet.{u}) n ≅ integralHomology (Δ[d] : SSet.{u}) n :=
  integralHomologyIsoOfPairContraction (Λ[d, k])
    (simplexMeetToIdentity k).h (simplexMeetToVertex k).h
    (simplexMeetToIdentity k).h₁
    ((simplexMeetToIdentity k).h₀.trans (simplexMeetToVertex k).h₀.symm)
    (fun a s t => simplexMeetToIdentity_mem_horn k a s.val s.property t)
    (fun a s t => simplexMeetToVertex_mem_horn k a s.val s.property t)
    (by
      rintro a x ⟨s, rfl⟩
      rw [(simplexMeetToVertex k).h₁]
      exact const_horn_vertex_mem k a s) n

/--
概要：正次元の horn 包含は全次数の整数ホモロジー同型を誘導する。
方針：構成した同型の順方向の射が実際の包含の誘導射であることを使う。
規約：整数係数の条件。局所係数と transfinite 添付への拡張は別工程。
使われ方：Kan 置換のホモロジー保存。
-/
theorem horn_integralHomologyIsomorphism {d : ℕ} [NeZero d] (k : Fin (d + 1)) :
    IntegralHomologyIsomorphism (Λ[d, k] : (Δ[d] : SSet.{u}).Subcomplex).ι :=
  fun n => (hornIntegralHomologyIso k n).isIso_hom

end SerrePositivity.KST.Comparison
