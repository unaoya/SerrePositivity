module

public import SerrePositivity.CommutativeAlgebra.CompletelyFlatEquiv
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor
public import SerrePositivity.HomologicalAlgebra.TorAcyclicBaseChangeComparison

/-!
# André E1・E2：正則主剰余から二元完全平坦性を戻す

## 概要

d が基底環と係数加群で正則なら、mod d の a 完全平坦性から元の (a,d) 完全平坦性が従う。
BS Rem 7.15（著者版 p.62）の実候補の導来剰余を δ 完全化へ渡す一般計算。

## 方針

正則性で mod d の高次 Tor を消し、d で消える試験加群の Tor を底変換後に計算する。

## 規約

完備性・Noether 性・通常平坦性は要求しない。

## 使われ方

H/d の p 完全平坦性を実完備化 H の (p,d) 完全平坦性へ戻す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard

/-- 概要：完全平坦な加群の定義イデアルによる標準底変換は高次 Tor を持たない。
方針：イデアルで消える標準係数加群を試験加群に取って Tor の対称性を使う。
規約：イデアルは任意。
使われ方：BS Rem 7.15（著者版 p.62）の実導来還元の離散性。 -/
theorem scalarExtensionTorVanishing_of_completelyFlat
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (hM : IsCompletelyFlat I M) : scalarExtensionTorVanishing (Ideal.Quotient.mk I) M := by
  let : Module R (R ⧸ I) := Module.compHom (R ⧸ I) (Ideal.Quotient.mk I)
  have hN : ∀ r ∈ I, ∀ x : R ⧸ I, r • x = 0 := by
    intro r hr x
    change Ideal.Quotient.mk I r * x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
  intro i hi
  have : Subsingleton (TorModule R i M (R ⧸ I)) :=
    (isConcentratedInDegreeZero_derivedTensor_iff M (R ⧸ I)).mp (hM (R ⧸ I) hN) i hi
  have : Subsingleton (TorModule R i (R ⧸ I) M) :=
    (torModuleComm (R := R) i (R ⧸ I) M).injective.subsingleton
  have hz : IsZero (((Tor (ModuleCat R) i).obj (ModuleCat.of R (R ⧸ I))).obj M) :=
    ModuleCat.isZero_of_subsingleton _
  let e : baseChangeScalarModule (Ideal.Quotient.mk I) ≃ₗ[R] (R ⧸ I) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact hz.of_iso (((Tor (ModuleCat R) i).mapIso e.toModuleIso).app M)

/-- 概要：正則主剰余の a 完全平坦性は元の (a,d) 完全平坦性を与える。
方針：d で消える試験加群に商作用を入れ、Tor 非輪状底変換で剰余の Tor 消滅を戻す。
規約：基底と係数加群の d 正則性を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の完全化前後の導来剰余比較。 -/
theorem completelyFlat_pair_of_regular_principal_reduction
    {R : Type u} [CommRing R] (a d : R) (hd : IsSMulRegular R d)
    (M : ModuleCat.{u} R) (hMd : IsSMulRegular M d)
    (hred : IsCompletelyFlat (Ideal.span {Ideal.Quotient.mk (Ideal.span {d}) a})
      ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {d}))).obj M)) :
    IsCompletelyFlat (Ideal.span {a, d}) M := by
  let I : Ideal R := Ideal.span {d}
  let q := Ideal.Quotient.mk I
  let Mbar := (ModuleCat.extendScalars q).obj M
  have hTor := scalarExtensionTorVanishing_principal_of_regular d hd M hMd
  intro N _ _ hN
  apply (isConcentratedInDegreeZero_derivedTensor_iff M N).mpr
  intro i hi
  have hId : I ≤ Ideal.span {a, d} := Ideal.span_mono (by simp)
  have ht : Module.IsTorsionBySet R N (I : Set R) :=
    fun {x} {r} => hN r (hId r.property) x
  let := ht.module
  let NQ := ModuleCat.of (R ⧸ I) N
  have hspan : Ideal.span {q a} ≤ Module.annihilator (R ⧸ I) N := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply Module.mem_annihilator.mpr
    intro x
    change a • x = 0
    exact hN a (Ideal.subset_span (by simp)) x
  have hNa : ∀ r ∈ Ideal.span {q a}, ∀ x : N, r • x = 0 :=
    fun r hr x => Module.mem_annihilator.mp (hspan hr) x
  have : Subsingleton (TorModule (R ⧸ I) i Mbar N) :=
    (isConcentratedInDegreeZero_derivedTensor_iff Mbar N).mp (hred N hNa) i hi
  have : Subsingleton (TorModule (R ⧸ I) i N Mbar) :=
    (torModuleComm (R := R ⧸ I) i N Mbar).injective.subsingleton
  have hzQ' : IsZero (((Tor (ModuleCat (R ⧸ I)) i).obj NQ).obj Mbar) :=
    ModuleCat.isZero_of_subsingleton _
  have hz := ((ModuleCat.restrictScalars q).map_isZero hzQ').of_iso
    (torAcyclicBaseChangeIso q M hTor NQ i)
  let e : (ModuleCat.restrictScalars q).obj NQ ≃ₗ[R] N :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hz' : IsZero (((Tor (ModuleCat R) i).obj (ModuleCat.of R N)).obj M) :=
    hz.of_iso (((Tor (ModuleCat R) i).mapIso e.toModuleIso).app M).symm
  have : Subsingleton (TorModule R i N M) := ModuleCat.subsingleton_of_isZero hz'
  have : Subsingleton (TorModule R i M N) := (torModuleComm (R := R) i M N).injective.subsingleton
  infer_instance

end SerrePositivity.BhattScholze.Andre
