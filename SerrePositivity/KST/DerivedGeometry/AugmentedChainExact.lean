module

public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
概要：単一項複体への準同型から増大鎖複体の完全性を得る。
方針：零次数は準同型の核・余核判定、正次数は元の複体の完全性を用いる。
規約：実際の増大写像と全次数を保持する。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech 増大の完全性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type u} [Category.{v} A] [Abelian A]
  {K : ChainComplex A ℕ} {M : A} (f : K ⟶ (ChainComplex.single₀ A).obj M)

/--
概要：零次数の準同型は増大における完全性と epi を与える。
方針：短複体の片側が零の場合の準同型判定を使う。
規約：増大の射は元の鎖写像の零次数成分。
使われ方：TT §3、Toën §3.2 の増大 Čech の低次数。
-/
lemma chainAugmentation_exact_and_epi [QuasiIsoAt f 0] :
    (ShortComplex.mk (K.d 1 0) (f.f 0) ((ChainComplex.toSingle₀Equiv K M f).property)).Exact ∧
      Epi (f.f 0) := by
  have hq : QuasiIsoAt f 0 := inferInstance
  rw [ChainComplex.quasiIsoAt₀_iff] at hq
  have hs := (ShortComplex.quasiIso_iff_of_zeros' _ (by simp) (by simp) (by simp)).mp hq
  simpa [HomologicalComplex.shortComplexFunctor'] using hs

/--
概要：単一項複体への準同型により作った増大鎖複体は全次数で完全。
方針：零次数と第1次数は増大の完全性、それ以降は元の準同型の完全性を使う。
規約：増大の項を第0次数に挿入する Mathlib の構成。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech 分解。
-/
lemma chainAugment_acyclic_of_quasiIso [QuasiIso f] :
    (ChainComplex.augment K (f.f 0) ((ChainComplex.toSingle₀Equiv K M f).property)).Acyclic := by
  have hs := chainAugmentation_exact_and_epi f
  intro n
  cases n with
  | zero =>
    apply (HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp)).mpr
    apply (ShortComplex.exact_iff_epi _ (by simp [ChainComplex.augment])).mpr
    simpa [ChainComplex.augment] using hs.2
  | succ n =>
    cases n with
    | zero =>
      apply (HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)).mpr
      simpa [ChainComplex.augment, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'] using hs.1
    | succ n =>
      have he : K.ExactAt (n + 1) :=
        (quasiIsoAt_iff_exactAt' f (n + 1) (ChainComplex.exactAt_succ_single_obj _ n)).mp
          inferInstance
      have ht := (HomologicalComplex.exactAt_iff' K (n + 2) (n + 1) n (by simp) (by simp)).mp he
      apply (HomologicalComplex.exactAt_iff' _ (n + 3) (n + 2) (n + 1) (by simp) (by simp)).mpr
      simpa [ChainComplex.augment, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', Nat.add_assoc] using ht

end SerrePositivity.KST.DerivedGeometry
