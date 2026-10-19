module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
概要：三角の第 2 射が前次数で全射ならファイバーのコホモロジーは核となる。
方針：長完全列から第 1 射の単射性を得て、短複体の完全性で核の普遍性を示す。
規約：差分射の全射性は適用先で実際に検証する。
使われ方：TT §3・§8、Toën §3.2、Stacks 15.88.12・36.3.4 の Milnor 列の消滅後の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Pretriangulated
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (n : ℤ)

include hT

/--
概要：前次数の第 2 射が全射なら第 1 射は指定次数で単射。
方針：長完全列の連結射が零であることを前後の同値で移す。
規約：任意の区別三角を許す。
使われ方：TT §3、Stacks 36.3.4 の導来逆極限の比較。
-/
lemma derivedTriangle_homology_mor₁_mono_of_epi_mor₂
    [Epi ((DerivedCategory.homologyFunctor C (n - 1)).map T.mor₂)] :
    Mono ((DerivedCategory.homologyFunctor C n).map T.mor₁) := by
  let H := DerivedCategory.homologyFunctor C 0
  exact (H.homologySequence_mono_shift_map_mor₁_iff T hT (n - 1) n (by omega)).mpr
    ((H.homologySequence_epi_shift_map_mor₂_iff T hT (n - 1) n (by omega)).mp
      (by
        change Epi ((DerivedCategory.homologyFunctor C (n - 1)).map T.mor₂)
        infer_instance))

/--
概要：ファイバーのコホモロジーを第 2 射の核として計算する。
方針：前次数の全射性による単射性と長完全列の完全性を使う。
規約：核の同型の存在だけでなく核錐の普遍性を与える。
使われ方：TT §3・§8、Stacks 15.88.12・36.3.4 の Milnor 列。
-/
def derivedTriangleHomologyKernel
    [Epi ((DerivedCategory.homologyFunctor C (n - 1)).map T.mor₂)] :
    IsLimit (KernelFork.ofι ((DerivedCategory.homologyFunctor C n).map T.mor₁)
      ((DerivedCategory.homologyFunctor C 0).homologySequence_comp T hT n)) := by
  letI : Mono (((DerivedCategory.homologyFunctor C 0).shift n).map T.mor₁) :=
    derivedTriangle_homology_mor₁_mono_of_epi_mor₂ T hT n
  exact ((DerivedCategory.homologyFunctor C 0).homologySequence_exact₂ T hT n).fIsKernel

end SerrePositivity.KST.DerivedGeometry
