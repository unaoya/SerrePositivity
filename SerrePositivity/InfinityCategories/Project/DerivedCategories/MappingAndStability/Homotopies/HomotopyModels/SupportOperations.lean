module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.SupportClosure

/-! # 台つき部分圏の正本上の演算

概要：D_Z と Perf_Z の実際の頂点上にシフト・cone・fiber・有限直和を構成する。
方針：全頂点条件を取り出し、モデルの閉性を全部分単体集合へ戻す。
規約：標準の dg モデルを使う。使われ方：台つき部分圏の閉性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (S : Type u) [CommRing S] (Z : TopologicalSpace.Closeds (PrimeSpectrum S))

/-- 概要：台つきモデルを正本の頂点にする。
方針：充満 dg nerve の定値頂点を像の同型で移す。
規約：同じ複体。使われ方：閉性の演算の出力。 -/
def supportedInfinityVertex (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SupportedSemifree S Z) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportCategory S Z) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportProperty S Z)).hom.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P)

/-- 概要：正本の台つき頂点の複体を取り出す。
方針：部分型の条件を唯一の頂点で評価する。
規約：代表を変更しない。使われ方：閉性の演算の入力。 -/
def supportedInfinityRepresentative (x :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportCategory S Z) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SupportedSemifree S Z :=
  ⟨x.val.obj 0, x.property 0⟩

/-- 概要：台つき頂点の任意整数シフト。
方針：モデルのシフト閉性。規約：D3 のシフト。使われ方：シフト閉性。 -/
def supportedInfinityShift (x :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportCategory S Z) _⦋0⦌) (n : ℤ) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportCategory S Z) _⦋0⦌ :=
  supportedInfinityVertex S Z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportedSemifreeShift S Z (supportedInfinityRepresentative S Z x) n)

/-- 概要：台つき二頂点間の任意の鎖写像の cone。
方針：モデルの cone 閉性。規約：標準 mapping cone。使われ方：cone 閉性。 -/
def supportedInfinityCone (x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportCategory S Z) _⦋0⦌)
    (f : (x.val.obj 0).val ⟶ (y.val.obj 0).val) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportCategory S Z) _⦋0⦌ :=
  supportedInfinityVertex S Z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportedSemifreeCone S Z
    (supportedInfinityRepresentative S Z x) (supportedInfinityRepresentative S Z y) f)

/-- 概要：台つき二頂点間の任意の鎖写像の fiber。
方針：cone の −1 シフト。規約：D4 のモデル。使われ方：fiber 閉性。 -/
def supportedInfinityFiber (x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportCategory S Z) _⦋0⦌)
    (f : (x.val.obj 0).val ⟶ (y.val.obj 0).val) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportCategory S Z) _⦋0⦌ :=
  supportedInfinityVertex S Z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportedSemifreeFiber S Z
    (supportedInfinityRepresentative S Z x) (supportedInfinityRepresentative S Z y) f)

/-- 概要：台つき有限族の直和。
方針：モデルの有限直和閉性。規約：空族も含む。使われ方：有限直和閉性。 -/
def supportedInfinityFiniteBiproduct {I : Type v} [Finite I] [Small.{u} I]
    (x : I → (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportCategory S Z) _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportCategory S Z) _⦋0⦌ :=
  supportedInfinityVertex S Z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.supportedSemifreeFiniteBiproduct S Z
    (fun i => supportedInfinityRepresentative S Z (x i)))

/-- 概要：台つきモデルを正本の頂点にする。
方針：充満 dg nerve の定値頂点を像の同型で移す。
規約：同じ複体。使われ方：閉性の演算の出力。 -/
def perfectSupportedInfinityVertex (P :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectSupportedSemifree S Z) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory S Z) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportProperty S Z)).hom.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P)

/-- 概要：正本の台つき頂点の複体を取り出す。
方針：部分型の条件を唯一の頂点で評価する。
規約：代表を変更しない。使われ方：閉性の演算の入力。 -/
def perfectSupportedInfinityRepresentative (x :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory S Z) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PerfectSupportedSemifree S Z :=
  ⟨x.val.obj 0, x.property 0⟩

/-- 概要：台つき頂点の任意整数シフト。
方針：モデルのシフト閉性。規約：D3 のシフト。使われ方：シフト閉性。 -/
def perfectSupportedInfinityShift (x :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory S Z) _⦋0⦌) (n : ℤ) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory S Z) _⦋0⦌ :=
  perfectSupportedInfinityVertex S Z
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportedSemifreeShift S Z (perfectSupportedInfinityRepresentative S Z x) n)

/-- 概要：台つき二頂点間の任意の鎖写像の cone。
方針：モデルの cone 閉性。規約：標準 mapping cone。使われ方：cone 閉性。 -/
def perfectSupportedInfinityCone (x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory S Z) _⦋0⦌)
    (f : (x.val.obj 0).val ⟶ (y.val.obj 0).val) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory S Z) _⦋0⦌ :=
  perfectSupportedInfinityVertex S Z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportedSemifreeCone S Z
    (perfectSupportedInfinityRepresentative S Z x) (perfectSupportedInfinityRepresentative S Z y) f)

/-- 概要：台つき二頂点間の任意の鎖写像の fiber。
方針：cone の −1 シフト。規約：D4 のモデル。使われ方：fiber 閉性。 -/
def perfectSupportedInfinityFiber (x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory S Z) _⦋0⦌)
    (f : (x.val.obj 0).val ⟶ (y.val.obj 0).val) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory S Z) _⦋0⦌ :=
  perfectSupportedInfinityVertex S Z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportedSemifreeFiber S Z
    (perfectSupportedInfinityRepresentative S Z x) (perfectSupportedInfinityRepresentative S Z y) f)

/-- 概要：台つき有限族の直和。
方針：モデルの有限直和閉性。規約：空族も含む。使われ方：有限直和閉性。 -/
def perfectSupportedInfinityFiniteBiproduct {I : Type v} [Finite I] [Small.{u} I]
    (x : I → (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory S Z) _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory S Z) _⦋0⦌ :=
  perfectSupportedInfinityVertex S Z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportedSemifreeFiniteBiproduct S Z
    (fun i => perfectSupportedInfinityRepresentative S Z (x i)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
