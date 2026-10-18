module

public import SerrePositivity.KST.DerivedGeometry.ResolutionTail
public import SerrePositivity.KST.DerivedGeometry.InjectiveHomExact

/-!
概要：鎖複体の Hom の正次数の完全性と射の因子分解の同値。
方針：加法群値の余鎖複体の完全性を元の圏の射の合成で展開する。
規約：標的の injectivity は要求しない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の Čech と Ext の有限次元移動の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type u} [Category.{v} A] [Abelian A] (K : ChainComplex A ℕ) (F : A)

/--
概要：鎖複体から対象への反変 Hom の加法群値の余鎖複体。
方針：鎖複体の対に加法的 Yoneda 関手を適用する。
規約：実際の合成から定まる微分を用いる。
使われ方：TT §3・§8、Toën §3.2 の Čech と次元移動。
-/
def chainHomComplex : CochainComplex AddCommGrpCat.{v} ℕ :=
  ((preadditiveYoneda.obj F).mapHomologicalComplex (.up ℕ)).obj K.op

/--
概要：Hom 余鎖複体の正次数の完全性は消える合成の因子分解と同値。
方針：同じ次数の短複体と加法群の完全性の元による表示を使う。
規約：全ての射について因子分解を得る。
使われ方：TT §3、Toën §3.2 の Ext の制限単射性の判定。
-/
lemma chainHom_exactAt_iff (n : ℕ) :
    (chainHomComplex K F).ExactAt (n + 1) ↔
      ∀ f : K.X (n + 1) ⟶ F, K.d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : K.X n ⟶ F, K.d (n + 1) n ≫ g = f := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  rfl

/--
概要：Hom の因子分解による正次数の完全性は通常の Hom 余鎖複体の完全性と同値。
方針：各次数の同値を全正次数について適用する。
規約：因子分解の述語と実際の複体を接続する。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の Cartan 型判定。
-/
lemma chainHomPositiveExact_iff : chainHomPositiveExact K F ↔
    ∀ n : ℕ, (chainHomComplex K F).ExactAt (n + 1) := by
  constructor
  · intro h n
    exact (chainHom_exactAt_iff K F n).mpr (h n)
  · intro h n
    exact (chainHom_exactAt_iff K F n).mp (h n)

end SerrePositivity.KST.DerivedGeometry
