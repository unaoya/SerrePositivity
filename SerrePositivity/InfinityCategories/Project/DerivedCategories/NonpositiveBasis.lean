module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeBasisEquivalence

/-! # 非正次数の自由複体の semibasis

概要：正次数で零かつ各次数で自由な複体は semifree である。
方針：各次数の基底に次数の負号の自然数値を高さとして与える。
規約：複体は下に非有界でもよい。使われ方：関手的自由解像度の semifree 性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable {S : Type u} [CommRing S]

/-- 概要：非正次数にある次数ごと自由な複体の高さ付き基底。
方針：正次数の微分の像は零、それ以外では次数が増すと高さが下がる。
規約：高さは (-k).toNat。使われ方：自由解像度の既存 semifree 定義への転送。 -/
def nonpositiveFreeBasis (P : Complex S) (hfree : ∀ k, Module.Free S (P.X k))
    (hzero : ∀ k : ℤ, 0 < k → IsZero (P.X k)) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis S P where
  Index k := letI := hfree k; Module.Free.ChooseBasisIndex S (P.X k)
  basis k := letI := hfree k; Module.Free.chooseBasis S (P.X k)
  height k _ := (-k).toNat
  lowering k i j hj := by
    have hk : k < 0 := by
      by_contra hn
      haveI := ModuleCat.subsingleton_of_isZero (hzero (k + 1) (by omega))
      have hz : (P.d k (k + 1)) ((letI := hfree k; Module.Free.chooseBasis S (P.X k)) i) = 0 :=
        Subsingleton.elim _ _
      have hne := Finsupp.mem_support_iff.mp hj
      apply hne
      rw [hz, map_zero, Finsupp.zero_apply]
    change (-(k + 1)).toNat < (-k).toNat
    omega

/-- 概要：非正次数で次数ごと自由な複体は semifree である。
方針：次数から構成した高さ付き基底を既存 filtration に移す。
規約：自由性と正次数零以外の前提なし。使われ方：関手的 semifree 解像度。 -/
theorem complexSemifree_of_nonpositive_free (P : Complex S)
    (hfree : ∀ k, Module.Free S (P.X k)) (hzero : ∀ k : ℤ, 0 < k → IsZero (P.X k)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S P :=
  (nonpositiveFreeBasis P hfree hzero).complexSemifree

end SerrePositivity.InfinityCategories.Project.DerivedCategories
