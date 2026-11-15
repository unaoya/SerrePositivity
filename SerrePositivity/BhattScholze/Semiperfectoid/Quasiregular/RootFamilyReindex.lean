module

public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootFamilyBase
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons

/-!
# 根付き変数の添字の同値

## 概要
添字の同値を、生の根付き環と実 H⁰ 完備化へ移す。
## 方針
有限台関数の添字変更と、既存の完備化の環同型を使う。
## 規約
BS 著者版 Proposition 7.10。Fin r とその宇宙持ち上げの照合にも使う。
## 使われ方
有限 T の本体模型と drafts の ULift 添字模型との比較。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.DerivedCompletion _root_.SerrePositivity.BhattScholze.Andre
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R]
variable {J : Type} {K : Type u} (e : J ≃ K)

/-- 添字同値による生の根付き変数環の同型。 -/
def rootFamilyRawReindex : rootFamilyRaw p R J ≃+* rootFamilyRaw p R K :=
  AddMonoidAlgebra.mapDomainRingEquiv R (Finsupp.domCongr e)

/-- 実完備化後の添字同値。 -/
def rootFamilyBaseReindex : rootFamilyBase p R J ≃+* rootFamilyBase p R K :=
  principalCompletionRingEquiv (rootFamilyRawReindex p R e) _ _ (map_natCast _ p)

/-- 添字変更は完備化の単位と両立する。 -/
theorem rootFamilyBaseReindex_unit (x : rootFamilyRaw p R J) :
    rootFamilyBaseReindex p R e (rootFamilyUnit p R J x) =
      rootFamilyUnit p R K (rootFamilyRawReindex p R e x) :=
  principalCompletionRingEquiv_unit _ _ _ _ x

/-- 添字変更は各段の根を対応する根へ送る。 -/
theorem rootFamilyBaseReindex_variable (j : J) (n : ℕ) :
    rootFamilyBaseReindex p R e (rootFamilyVariable p R J j n) =
      rootFamilyVariable p R K (e j) n := by
  rw [rootFamilyVariable, rootFamilyBaseReindex_unit]
  change rootFamilyUnit p R K ((rootFamilyRawReindex p R e)
    (AddMonoidAlgebra.single _ 1)) = _
  rw [rootFamilyRawReindex, AddMonoidAlgebra.mapDomainRingEquiv_single]
  congr 1
  congr 1
  simp [Finsupp.domCongr]

end SerrePositivity.BhattScholze.Semiperfectoid
