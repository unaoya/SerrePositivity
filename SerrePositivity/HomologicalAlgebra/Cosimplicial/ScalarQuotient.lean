module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.ModuleMap
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient
public import SerrePositivity.CommutativeAlgebra.Koszul.Basic
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.ModuleMap
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# 余単体的環の通常スカラー商の短完全列

## 概要
基底のスカラーの像で各項を割ると、線形な交代余面複体の短完全列を得る。

## 方針
既存の商の余単体射を台加群に移し、核・像と全射性を項ごとに確認する。

## 規約
スカラーの正則性は各環の項で仮定する。

## 使われ方
BS 著者版 Theorem 6.4 の実際の mod p 比較からの持ち上げ。
-/

public noncomputable section

open CategoryTheory HomologicalComplex AlgebraicTopology
open scoped Simplicial

universe u

namespace SerrePositivity.Cosimplicial

set_option backward.isDefEq.respectTransparency false

variable (k : Type u) [CommRing k] (X : CosimplicialObject CommRingCat.{u})
variable (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ X)
variable (a : k) (d : ∀ n, X.obj n)
variable (hd : ∀ {m n} (θ : m ⟶ n), X.map θ (d m) = d n)
variable (hbase : ∀ n, (ι.app n).hom a = d n)

local notation "K" => Functor.obj (alternatingCofaceMapComplex (ModuleCat k)) (toModules k X ι)
local notation "Q" => quotPow X d hd 1
local notation "q" => quotProjection X d hd 1
local notation "KQ" => Functor.obj (alternatingCofaceMapComplex (ModuleCat k))
  (toModules k (Q) (ι ≫ q))

/-- 実際の環の商射が誘導する、基底線形な交代余面複体の射。 -/
def scalarQuotientCochainProjection : K ⟶ KQ :=
  moduleCochainMap k ι (ι ≫ q) q rfl

include hbase in
/-- スカラー作用に環の商射を続けると零になる。 -/
theorem scalarQuotientCochainProjection_zero :
    (a • 𝟙 K) ≫ scalarQuotientCochainProjection k X ι d hd = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change X.obj ⦋i⦌ at x
  change Ideal.Quotient.mk (Ideal.span {d ⦋i⦌ ^ 1}) ((ι.app ⦋i⦌).hom a * x) = 0
  rw [hbase]
  apply (Ideal.Quotient.eq_zero_iff_mem).mpr
  apply Ideal.mem_span_singleton.mpr
  exact ⟨x, by rw [pow_one]⟩

/-- 項ごとに正則なスカラーの通常商は、線形な交代余面複体の短完全列を与える。 -/
theorem scalarQuotientCochainProjection_shortExact
    (hr : ∀ n, Function.Injective (fun x : X.obj n => d n * x)) :
    (CategoryTheory.ShortComplex.mk ((a • 𝟙 K))
      (scalarQuotientCochainProjection k X ι d hd)
      (scalarQuotientCochainProjection_zero k X ι a d hd hbase)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    change X.obj ⦋i⦌ at x
    change Ideal.Quotient.mk (Ideal.span {d ⦋i⦌ ^ 1}) x = 0 at hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem).mp hx)
    refine ⟨y, ?_⟩
    change (ι.app ⦋i⦌).hom a * y = x
    rw [hbase]
    simpa only [pow_one] using hy.symm
  · apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (fun x : X.obj ⦋i⦌ => (ι.app ⦋i⦌).hom a * x)
    rw [hbase]
    exact hr ⦋i⦌
  · apply (ModuleCat.epi_iff_surjective _).mpr
    change Function.Surjective (Ideal.Quotient.mk (Ideal.span {d ⦋i⦌ ^ 1}))
    exact Ideal.Quotient.mk_surjective

end SerrePositivity.Cosimplicial
