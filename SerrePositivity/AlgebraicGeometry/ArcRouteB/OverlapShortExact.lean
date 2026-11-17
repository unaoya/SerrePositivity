module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.OverlapComplex
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Milnor.ArcMilnorTensor
public import SerrePositivity.HomologicalAlgebra.PerfectRingTor
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
概要：任意の完全係数Tで、指定した重なりの係数列が短完全になることを示す。
方針：完全環のTor消滅で元の列をtensorし、単位・積の標準同型でT係数の列へ戻す。
規約：Tは平坦と仮定しない。加法群へ忘れて同じ写像を比較し、T加群での完全性を反映する。
使われ方：2iのO05、BM18 Proposition 4.8(5)の構造層での普遍貼り合わせ。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity
open SerrePositivity.BhattScholze.Perfectoidization
open scoped TensorProduct
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 計画O05：完全係数ではTor消滅により、同じ重なりの列が短完全になる。 -/
theorem overlapTensorModuleComplex_shortExact
    (p : ℕ) [Fact p.Prime] {V T : Type u} [CommRing V] [IsDomain V]
    [ValuationRing V] [CommRing T] [Algebra V T] [PerfectRing V p]
    [PerfectRing T p] (hp : (p : V) = 0)
    {a b : PrimeSpectrum V} (h : a ≤ b) :
    (overlapTensorModuleComplex (T := T) h).ShortExact := by
  let L := Localization.AtPrime b.asIdeal
  let Q := V ⧸ a.asIdeal
  let I := ValuationIntervalRing h
  let S0 := Arc.overlapModuleComplex h
  let ST := overlapTensorModuleComplex (T := T) h
  letI : PerfectRing I p := perfectRing_interval h p hp
  have hTor : Subsingleton (TorModule V 1 T S0.X₃) :=
    perfectRing_tor_subsingleton_of_char_eq_zero p V hp T I 1 (by decide)
  have ht := Arc.shortExact_tensorLeft_of_tor T S0 (Arc.overlapModuleComplex_shortExact h) hTor
  let S1 := (S0.map (tensorLeft (ModuleCat.of V T))).map (forget₂ (ModuleCat V) AddCommGrpCat)
  let S2 := ST.map (forget₂ (ModuleCat T) AddCommGrpCat)
  have h1 : S1.ShortExact := ht.map_of_exact (forget₂ (ModuleCat V) AddCommGrpCat)
  let e1 : S1.X₁ ≅ S2.X₁ := (TensorProduct.rid V T).toAddEquiv.toAddCommGrpIso
  let e2 : S1.X₂ ≅ S2.X₂ := (TensorProduct.prodRight V V T L Q).toAddEquiv.toAddCommGrpIso
  let e3 : S1.X₃ ≅ S2.X₃ := Iso.refl _
  have e : S1 ≅ S2 := ShortComplex.isoMk e1 e2 e3 (by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    refine TensorProduct.inductionOn x ?_ ?_
    · intro t v
      change T at t
      change V at v
      change ((v • t) ⊗ₜ[V] (1 : L), (v • t) ⊗ₜ[V] (1 : Q)) =
        (t ⊗ₜ[V] algebraMap V L v, t ⊗ₜ[V] algebraMap V Q v)
      apply Prod.ext
      · simpa only [Algebra.smul_def, mul_one] using
          (TensorProduct.smul_tmul (R := V) v t (1 : L))
      · simpa only [Algebra.smul_def, mul_one] using
          (TensorProduct.smul_tmul (R := V) v t (1 : Q))
    · intro x y hx hy
      simp only [map_add, hx, hy]) (by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    refine TensorProduct.inductionOn x ?_ ?_
    · intro t z
      change T at t
      change L × Q at z
      change (t ⊗ₜ[V] Arc.localizationToInterval h z.1) -
        (t ⊗ₜ[V] algebraMap Q I z.2) =
        t ⊗ₜ[V] (Arc.localizationToInterval h z.1 - algebraMap Q I z.2)
      exact (TensorProduct.tmul_sub t _ _).symm
    · intro x y hx hy
      simp only [map_add, hx, hy])
  have h2 : S2.ShortExact := ShortComplex.shortExact_of_iso e h1
  apply ModuleCat.shortComplex_shortExact
  · exact (ShortComplex.ab_exact_iff_function_exact S2).mp h2.exact
  · exact (AddCommGrpCat.mono_iff_injective S2.f).mp h2.mono_f
  · exact (AddCommGrpCat.epi_iff_surjective S2.g).mp h2.epi_g

end SerrePositivity.AlgebraicGeometry.ArcRouteB
