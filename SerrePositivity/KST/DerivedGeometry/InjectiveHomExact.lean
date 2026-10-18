module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Opposite

/-!
概要：injective 対象への Hom が複体の完全性を保つことを証明する。
方針：短複体の射の因子分解を injectivity で延長する。
規約：Hom の完全性を未証明のフィールドにしない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の自由 Čech 分解への Hom。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type u} [Category.{v} A] [Abelian A] (I : A) [Injective I]

/--
概要：完全な短複体に injective 対象への反変 Hom を適用すると完全。
方針：消える合成を持つ射を元の完全性で因子分解し、injectivity で延長する。
規約：加法群値の実際の preadditive Yoneda 関手を使う。
使われ方：TT §3・§8、Toën §3.2 の Čech 鎖複体から余鎖複体への移送。
-/
lemma injectiveHom_op_exact (S : ShortComplex A) (hS : S.Exact) :
    (S.op.map (preadditiveYoneda.obj I)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro f hf
  exact ⟨hS.descToInjective f hf, hS.comp_descToInjective f hf⟩

/--
概要：injective 対象への加法的 Yoneda 関手は短複体の完全性を保つ。
方針：元の圏の短複体へ対を取り、証明済みの反変 Hom の完全性を使う。
規約：対圏上の任意の短複体について述べる。
使われ方：TT §3、Toën §3.2 の injective Hom の複体への適用。
-/
lemma injectiveHom_map_exact (S : ShortComplex Aᵒᵖ) (hS : S.Exact) :
    (S.map (preadditiveYoneda.obj I)).Exact :=
  injectiveHom_op_exact I S.unop hS.unop

/--
概要：injective 対象への Hom は任意の完全な複体を完全な複体へ送る。
方針：各次数の短複体に Hom の完全性を適用する。
規約：添字と複体形状の有界性に条件を付けない。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech 増大への Hom。
-/
lemma injectiveHom_map_acyclic {ι : Type w} {c : ComplexShape ι}
    (K : HomologicalComplex Aᵒᵖ c) (hK : K.Acyclic) :
    (((preadditiveYoneda.obj I).mapHomologicalComplex c).obj K).Acyclic :=
  fun n => injectiveHom_map_exact I (K.sc n) (hK n)

end SerrePositivity.KST.DerivedGeometry
