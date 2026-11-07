-- 移行先：SerrePositivity.BhattScholze.Perfectoidization.Derived.RootAdjunction。
module

public import SerrePositivity.BhattScholze.Perfectoidization.Derived.RootAdjunction
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic

/-!
# 根添加の残る定理

## 概要
濃度、完備・代数的根添加の関手性と filtered 余極限、有限変数の根添加環の
perfectoid 性と完全忠実平坦性を扱う。

## 方針
移行済みの構成・延長性・mod p の根の結果を利用する。
設計は a5-design.md §3.1〜§3.3。

## 規約
本ファイルは drafts として保持する。

## 使われ方
A5-4 の弱始対象と降下、A6-1 の perfectoid 被覆。
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- 概要：(iii) #S̃ ≤ (#S + ℵ₀)^{ℵ₀}（各段は #S_k + ℵ₀ 個の変数の多項式環の商、可算余極限、完備化は可算列の逆極限）。
方針：各段の濃度評価と完備化の濃度（A0 `cardinal_envelope_le` と同型の議論）。
規約：κ = `cutoff` 以上の κ（`IsAdmissibleCutoff`、κ^{ℵ₀} = κ）なら ≤ κ。
使われ方：κ 側の site の対象になること（D47）。 -/
theorem rootClosure_cardinal_le : Cardinal.mk (rootClosure p R S) ≤ (Cardinal.mk S + Cardinal.aleph0) ^ Cardinal.aleph0 := by
  sorry -- 可算個の段と可算完備化の濃度評価

/-- 概要：(iv) S ↦ S̃ は関手的（段ごとに X_a ↦ X_{f(a)}、Y_a ↦ Y_{f(a)}）。
**完備化した filtered 余極限とは可換でない**（W9-II-09：完備化で現れる元に付く独立な Y 変数が有限段から来ない。反例 R = Z_p[p^{1/p^∞}]^∧、S_n = R⟨t_1..t_n⟩、
s = Σ p^j t_j）。旧 `rootClosure_filteredColimit` は撤回。filtered 余極限の段は下の `algebraicRootClosure` を使う。
方針：段ごとの関手性。
規約：—
使われ方：弱始対象の関手性のみ。 -/
def rootClosureMap {S' : Type u} [CommRing S'] [Algebra R S'] (f : S →+* S') : rootClosure p R S →+* rootClosure p R S' := by
  sorry -- 完備化した各段の変数を f で再添字付けし、余極限と完備化で送る
theorem rootClosureMap_comp_unit {S' : Type u} [CommRing S'] [Algebra R S'] (f : S →+* S') :
    (rootClosureMap p R S f).comp (rootClosureUnit p R S) = (rootClosureUnit p R S').comp f := by
  sorry -- 第零段の構造射の自然性
theorem rootClosureMap_id : rootClosureMap p R S (RingHom.id S) = RingHom.id _ := by
  sorry -- 各段の再添字付けが恒等射
theorem rootClosureMap_comp {S' S'' : Type u} [CommRing S'] [Algebra R S'] [CommRing S''] [Algebra R S'']
    (f : S →+* S') (g : S' →+* S'') :
    rootClosureMap p R S (g.comp f) = (rootClosureMap p R S' g).comp (rootClosureMap p R S f) := by
  sorry -- 各段の再添字付けの合成を完備化で送る

def algebraicStageMap {C C' : CommRingCat.{u}} (f : C ⟶ C') :
    ∀ n, algebraicStages p C n ⟶ algebraicStages p C' n
  | 0 => f
  | n + 1 => by
    let g := (algebraicStageMap f n).hom
    let rename := MvPolynomial.eval₂Hom (MvPolynomial.C.comp g)
      (fun j => MvPolynomial.X (Sum.map g g j))
    exact CommRingCat.ofHom (Ideal.quotientMap (algebraicStepIdeal p (algebraicStages p C' n))
      rename (by sorry)) -- a−X_a^p−pY_a は g(a) の関係に移る

def algebraicTowerMap {C C' : CommRingCat.{u}} (f : C ⟶ C') :
    algebraicTower p C ⟶ algebraicTower p C' :=
  NatTrans.ofSequence (algebraicStageMap p f) (by
    sorry) -- 係数の包含は g と可換なので後続段への正方形が可換

def algebraicRootClosureMap {C C' : Type u} [CommRing C] [CommRing C'] (f : C →+* C') :
    algebraicRootClosure p C →+* algebraicRootClosure p C' :=
  (Limits.colim.map (algebraicTowerMap p (CommRingCat.ofHom f))).hom

def algebraicRootFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj C := Limits.colimit (algebraicTower p C)
  map f := Limits.colim.map (algebraicTowerMap p f)
  map_id := by sorry -- 各段で恒等射
  map_comp := by sorry -- 係数と変数の添字で合成を保つ

/-- 概要：E(−) は通常の環の filtered 余極限と可換（各元と各等式が有限個の変数と関係だけを使うので）。
方針：`MvPolynomial` の余極限との交換。filtered 図式の標準射 `colimit.post` の可逆性で述べる。
規約：—
使われ方：A5-4 `algebraicRootCover_properties`。 -/
theorem algebraicRootClosure_filteredColimit {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{u}) : IsIso (Limits.colimit.post D (algebraicRootFunctor p)) := by
  sorry -- 一つの多項式と関係の有限和は有限段から来る。各段の比較と ω 余極限を交換する

include hR in
/-- 概要：R perfectoid なら T_∞ は perfectoid（R⟨X^{1/p^∞}⟩ は R の perfectoid 性を継ぐ：p 完備、ϖ は R から、mod p の Frobenius は変数の根で全射、
核は R の核の生成元で生成）。
方針：一変数の `compatibleRootCompletion_isIntegralPerfectoid` の計算を有限個の根変数で行う。
規約：—
使われ方：Lemma 8.6 の T_∞ 側（L_{T_∞/R}^∧ = 0）、A5-4 の S̃ の semiperfectoid 性。 -/
theorem polyRootAlgebra_isIntegralPerfectoid (r : ℕ) : IsIntegralPerfectoid (polyRootAlgebra p R r) p := by
  sorry -- 基底の擬一様化元と変数の根から各条件を得る

include hR in
/-- 概要：T → T_∞ は p 完備忠実平坦（T_∞ は T 上、単項式 X^{a}（a ∈ (ℤ[1/p] ∩ [0,1))^r）を基底とする自由加群の p 完備化）。よって S → S̃ も。
方針：基底の明示。
規約：記録（降下の前提は Lemma 8.6 の descendability で、忠実平坦性は直接は使わない）。
使われ方：原典 (3) との対応。 -/
theorem polyAlgebraToRoot_pCompletelyFaithfullyFlat (r : ℕ) :
    letI := (polyAlgebraToRoot p R r).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : polyAlgebra p R r)}) (polyRootAlgebra p R r) := by
  sorry -- p 冪分母で各座標が [0,1) の指数をもつ単項式が完備自由基底。mod p は 1 を含む自由基底をもつ

end SerrePositivity.BhattScholze.Perfectoidization.Derived
