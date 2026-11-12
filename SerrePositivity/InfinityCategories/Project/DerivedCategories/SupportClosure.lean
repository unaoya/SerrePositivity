module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SupportBasic

/-! # 台つき semifree 複体の閉性

概要：D_Z と Perf_Z のモデルは零・シフト・cone・fiber・有限直和で閉じる。
方針：semifree 性、完全性、コホモロジーの台の各閉性を組み合わせる。
規約：閉集合 Z は任意。使われ方：台つき ∞ 部分圏での標準 dg 演算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
open scoped ZeroObject
variable (S : Type u) [CommRing S] (Z : TopologicalSpace.Closeds (PrimeSpectrum S))

/-- 概要：Z に台を持つ semifree 複体のモデル。
方針：対象条件による充満部分圏を取る。規約：元の Hom 複体。使われ方：D_Z の演算。 -/
abbrev SupportedSemifree := DGFullSubcategory (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportProperty S Z)

/-- 概要：Z に台を持つ完全 semifree 複体のモデル。
方針：完全性と台を同時に課す。規約：有限射影代表。使われ方：Perf_Z の演算。 -/
abbrev PerfectSupportedSemifree := DGFullSubcategory (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportProperty S Z)

/-- 概要：零複体は任意の Z に台を持つ semifree 複体である。
方針：零ホモロジーと semifree 零複体を使う。
規約：空の台も含む。使われ方：D_Z の零対象モデル。 -/
def supportedSemifreeZero : SupportedSemifree S Z :=
  ⟨⟨0, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_zero S⟩, hasHomologySupportOn_of_isZero (isZero_zero _)⟩

/-- 概要：零複体は任意の Z に台を持つ完全 semifree 複体である。
方針：二つの零複体の条件を組にする。
規約：同じ零複体。使われ方：Perf_Z の零対象モデル。 -/
def perfectSupportedSemifreeZero : PerfectSupportedSemifree S Z :=
  ⟨(supportedSemifreeZero S Z).val,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel_zero S, (supportedSemifreeZero S Z).property⟩

/-- 概要：D_Z のモデルは任意整数シフトで閉じる。
方針：semifree 性と台のシフト閉性。規約：D3 のシフト。使われ方：シフトのモデル。 -/
def supportedSemifreeShift (P : SupportedSemifree S Z) (n : ℤ) : SupportedSemifree S Z :=
  ⟨⟨P.val.val⟦n⟧, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_shift S P.val.property n⟩, P.property.shift n⟩

/-- 概要：D_Z のモデルの任意の射の cone は D_Z のモデルである。
方針：semifree の cone 閉性とホモロジー長完全列を使う。
規約：任意の鎖写像。使われ方：cone 閉性。 -/
def supportedSemifreeCone (P Q : SupportedSemifree S Z) (f : P.val.val ⟶ Q.val.val) :
    SupportedSemifree S Z :=
  ⟨⟨CochainComplex.mappingCone f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_mappingCone f P.val.property Q.val.property⟩,
    P.property.mappingCone f Q.property⟩

/-- 概要：D_Z のモデルの任意の射の fiber は D_Z のモデルである。
方針：cone の −1 シフト。規約：D4 の標準 fiber。使われ方：fiber 閉性。 -/
def supportedSemifreeFiber (P Q : SupportedSemifree S Z) (f : P.val.val ⟶ Q.val.val) :
    SupportedSemifree S Z := supportedSemifreeShift S Z (supportedSemifreeCone S Z P Q f) (-1)

/-- 概要：D_Z のモデルは有限直和で閉じる。
方針：各対象条件の有限直和閉性を使う。
規約：小さい有限族。使われ方：有限直和のモデル。 -/
def supportedSemifreeFiniteBiproduct {I : Type v} [Finite I] [Small.{u} I]
    (P : I → SupportedSemifree S Z) : SupportedSemifree S Z :=
  ⟨⟨⨁ (fun i => (P i).val.val),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_finiteBiproduct S _ (fun i => (P i).val.property)⟩,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homologySupport_finiteBiproduct S Z _ (fun i => (P i).property)⟩

/-- 概要：Perf_Z のモデルは任意整数シフトで閉じる。
方針：完全性と台のシフト閉性を使う。規約：既存のシフト。使われ方：Perf_Z の演算。 -/
def perfectSupportedSemifreeShift (P : PerfectSupportedSemifree S Z) (n : ℤ) :
    PerfectSupportedSemifree S Z :=
  ⟨⟨P.val.val⟦n⟧, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_shift S P.val.property n⟩,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel_shift S P.property.1 n, P.property.2.shift n⟩

/-- 概要：Perf_Z のモデル間の任意の射の cone は同じ部分圏に属す。
方針：三つの対象条件の cone 閉性を組み合わせる。
規約：任意の鎖写像。使われ方：Perf_Z の cone 閉性。 -/
def perfectSupportedSemifreeCone (P Q : PerfectSupportedSemifree S Z)
    (f : P.val.val ⟶ Q.val.val) : PerfectSupportedSemifree S Z :=
  ⟨⟨CochainComplex.mappingCone f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_mappingCone f P.val.property Q.val.property⟩,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel_mappingCone S f P.property.1 Q.property.1,
    P.property.2.mappingCone f Q.property.2⟩

/-- 概要：Perf_Z のモデル間の任意の射の fiber は同じ部分圏に属す。
方針：cone の −1 シフト。規約：D4 の fiber。使われ方：Perf_Z の fiber 閉性。 -/
def perfectSupportedSemifreeFiber (P Q : PerfectSupportedSemifree S Z)
    (f : P.val.val ⟶ Q.val.val) : PerfectSupportedSemifree S Z :=
  perfectSupportedSemifreeShift S Z (perfectSupportedSemifreeCone S Z P Q f) (-1)

/-- 概要：Perf_Z のモデルは有限直和で閉じる。
方針：semifree 性・完全性・台のそれぞれの有限直和閉性を使う。
規約：小さい有限族。使われ方：Perf_Z の有限直和。 -/
def perfectSupportedSemifreeFiniteBiproduct {I : Type v} [Finite I] [Small.{u} I]
    (P : I → PerfectSupportedSemifree S Z) : PerfectSupportedSemifree S Z :=
  ⟨⟨⨁ (fun i => (P i).val.val),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_finiteBiproduct S _ (fun i => (P i).val.property)⟩,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel_finiteBiproduct S _ (fun i => (P i).property.1),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homologySupport_finiteBiproduct S Z _ (fun i => (P i).property.2)⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
