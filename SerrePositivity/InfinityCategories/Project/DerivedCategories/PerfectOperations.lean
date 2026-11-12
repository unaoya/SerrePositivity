module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectInclusion

/-! # Perf の頂点に対する閉性の演算

概要：Perf の実際の頂点からシフト・cone・fiber・有限直和の頂点を構成する。
方針：頂点の複体に付された完全性を取り出し、モデルの閉性を正本へ移す。
規約：cone と fiber は D(S) の標準 dg モデル。使われ方：G2 の完全対象の演算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (S : Type u) [CommRing S]

/-- 概要：完全 semifree 複体を正本の Perf の頂点にする。
方針：dg nerve の定値頂点を標準同型で移す。
規約：対象の複体を置き換えない。使われ方：閉性の演算の出力。 -/
def perfectInfinityVertex (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectSemifree S) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityCategory S) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModelIso S).hom.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P)

/-- 概要：正本に移した頂点の D(S) での像は元の semifree 複体の頂点である。
方針：標準同型と二つの包含の整合式を零次で評価する。
規約：実際の頂点の等式。使われ方：周囲の dg 演算との同定。 -/
lemma perfectInfinityVertex_inclusion (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectSemifree S) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityInclusion S).app _ (perfectInfinityVertex S P) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P.val := by
  have h := congrArg (fun f : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModel S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S =>
    f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectNerveModelIso_hom_inclusion S)
  exact h.trans (by apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective; rfl)

/-- 概要：Perf の任意の頂点の複体は完全 semifree 複体である。
方針：部分型の全頂点条件を唯一の対象で評価する。
規約：元の頂点の複体を保持する。使われ方：閉性の演算の入力。 -/
def perfectInfinityVertexRepresentative (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityCategory S) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectSemifree S := ⟨x.val.obj 0, x.property 0⟩

/-- 概要：Perf の頂点の任意整数シフトは Perf の頂点を持つ。
方針：元の複体のシフトを閉性で再び頂点にする。
規約：D3 の複体シフト。使われ方：シフト閉性の正本上の形。 -/
def perfectInfinityShift (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityCategory S) _⦋0⦌) (n : ℤ) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityCategory S) _⦋0⦌ :=
  perfectInfinityVertex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeShift S (perfectInfinityVertexRepresentative S x) n)

/-- 概要：Perf の二頂点間の任意の鎖写像の cone は Perf の頂点を持つ。
方針：完全 semifree 代表の cone 閉性を用いる。
規約：標準の mapping cone。使われ方：cone 閉性の正本上の形。 -/
def perfectInfinityCone (x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityCategory S) _⦋0⦌)
    (f : (x.val.obj 0).val ⟶ (y.val.obj 0).val) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityCategory S) _⦋0⦌ :=
  perfectInfinityVertex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeCone S
    (perfectInfinityVertexRepresentative S x) (perfectInfinityVertexRepresentative S y) f)

/-- 概要：Perf の二頂点間の任意の鎖写像の fiber は Perf の頂点を持つ。
方針：cone の −1 シフトを用いる。
規約：D4 の標準 fiber。使われ方：fiber 閉性の正本上の形。 -/
def perfectInfinityFiber (x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityCategory S) _⦋0⦌)
    (f : (x.val.obj 0).val ⟶ (y.val.obj 0).val) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityCategory S) _⦋0⦌ :=
  perfectInfinityVertex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeFiber S
    (perfectInfinityVertexRepresentative S x) (perfectInfinityVertexRepresentative S y) f)

/-- 概要：Perf の有限族の頂点の直和は Perf の頂点を持つ。
方針：完全 semifree 代表の有限直和を取る。
規約：空族も含む小さい有限族。使われ方：有限直和閉性の正本上の形。 -/
def perfectInfinityFiniteBiproduct {I : Type v} [Finite I] [Small.{u} I]
    (x : I → (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityCategory S) _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinityCategory S) _⦋0⦌ :=
  perfectInfinityVertex S
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeFiniteBiproduct S (fun i => perfectInfinityVertexRepresentative S (x i)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
