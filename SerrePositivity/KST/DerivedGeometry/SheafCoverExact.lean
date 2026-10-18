module

public import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
概要：層の開被覆上の切断と二重交叉の差から完全な短複体を作る。
方針：層条件の等化子を二つの制限の差の核へ移す。
規約：任意のアーベル圏の層・任意の被覆を扱う。
使われ方：TT §3・§8、Toën §3.2 の Čech 増大の零次数の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w a b
open CategoryTheory Limits Preadditive TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{w} A]
  {X : TopCat.{w}} (F : TopCat.Sheaf A X) {ι : Type w} (U : ι → Opens X)
open TopCat.Presheaf.SheafConditionEqualizerProducts

/--
概要：層の被覆上の制限と二つの交叉制限の差を短複体として束ねる。
方針：差と合成の分配則および制限の可換性を使う。
規約：左端は被覆の和集合上の実際の切断。
使われ方：TT §3・§8、Toën §3.2 の Čech 増大。
-/
def sheafCoverShortComplex : ShortComplex A :=
  ShortComplex.mk (res F.obj U) (leftRes F.obj U - rightRes F.obj U)
    (by rw [comp_sub, w F.obj U, sub_self])

/--
概要：層条件は被覆短複体の最初の射を差の核にする。
方針：Mathlib の等化子表示を差の核へ変換する。
規約：核は元の制限写像を持つ。
使われ方：TT §3、Toën §3.2 の零次数 Čech の普遍性。
-/
def sheafCoverKernel : IsLimit (KernelFork.ofι (sheafCoverShortComplex F U).f
    (sheafCoverShortComplex F U).zero) :=
  Preadditive.isLimitKernelForkOfFork
    (((TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts F.obj).mp F.property U).some)

/--
概要：層の被覆短複体は中央で完全。
方針：構成済みの実際の核の普遍性を使う。
規約：被覆の有限性・準連接性を要求しない。
使われ方：TT §3・§8、Toën §3.2 の貼り合わせの完全性。
-/
lemma sheafCoverShortComplex_exact : (sheafCoverShortComplex F U).Exact :=
  (sheafCoverShortComplex F U).exact_of_f_is_kernel (sheafCoverKernel F U)

/--
概要：被覆上の全制限を合わせた射は mono。
方針：層条件から得た核の射の単射性を使う。
規約：空の被覆も含む。
使われ方：TT §3・§8、Toën §3.2 の貼り合わせの一意性。
-/
instance sheafCoverShortComplex_mono : Mono (sheafCoverShortComplex F U).f :=
  mono_of_isLimit_fork (sheafCoverKernel F U)

end SerrePositivity.KST.DerivedGeometry
