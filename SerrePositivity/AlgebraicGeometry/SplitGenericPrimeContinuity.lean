module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.GeometricallyIntegralGenericFreeness
public import SerrePositivity.AlgebraicGeometry.SplitAlgebraCoefficientMembership
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
概要：KST §5、Stacks 0810・0811 の分裂表示を持つ代数の一般階数。
方針：係数による基本開集合の逆像を計算し、自由 locus の階数を引き戻す。
規約：分裂表示は実際の線形写像とその左逆元として入力する。
使われ方：一定階数の開集合へ分けて係数中心を選ぶ。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
  [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
  {ι : Type*} (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B)
  (hpe : p.comp e = LinearMap.id)

include e p hpe

/--
概要：拡大素点写像の基本開集合の逆像は各係数の基本開集合の和。
方針：拡大イデアルへの所属を全係数の所属で判定して否定する。
規約：KST §5、Stacks 0810・0811、分裂表示を明示する。
使われ方：拡大素点写像の連続性。
-/
theorem genericPrime_preimage_basicOpen (b : B) :
    (geometricallyIntegralGenericPrime A B) ⁻¹' (PrimeSpectrum.basicOpen b : Set _) =
      ⋃ i, (PrimeSpectrum.basicOpen (e b i) : Set (PrimeSpectrum A)) := by
  ext P
  simp only [Set.mem_preimage, Set.mem_iUnion]
  change b ∉ P.asIdeal.map (algebraMap A B) ↔ ∃ i, e b i ∉ P.asIdeal
  rw [splitAlgebra_mem_map_iff e p hpe P.asIdeal b]
  exact not_forall

/--
概要：実際の自由加群への分裂表示があると拡大素点写像は連続。
方針：基本開集合の逆像を係数の基本開集合の和で表す。
規約：KST §5、Stacks 0810・0811、分裂の存在を仮定する補助段階。
使われ方：一般点での自由階数を基礎環の素スペクトル上へ引き戻す。
-/
theorem continuous_geometricallyIntegralGenericPrime :
    Continuous (geometricallyIntegralGenericPrime A B) := by
  apply PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff.mpr
  rintro _ ⟨b, rfl⟩
  rw [genericPrime_preimage_basicOpen A B e p hpe b]
  exact isOpen_iUnion (fun _ => PrimeSpectrum.isOpen_basicOpen)

variable {M : Type*} [AddCommGroup M] [Module A M] [Module B M]
  [IsScalarTower A B M] [Module.Flat A M] [Module.FinitePresentation B M]

omit e p hpe in
/--
概要：拡大素点は基礎環上平坦な有限表示加群の自由 locus に属する。
方針：テンソル局所化の自由性を既存の自由 locus の所属判定へ渡す。
規約：KST §5、Stacks 0810・0811、この所属には分裂表示は不要。
使われ方：拡大素点への連続写像を自由 locus へ持ち上げる。
-/
theorem genericPrime_mem_freeLocus (P : PrimeSpectrum A) :
    geometricallyIntegralGenericPrime A B P ∈ Module.freeLocus B M := by
  let Q := geometricallyIntegralGenericPrime A B P
  let L := Localization.AtPrime Q.asIdeal
  have hf : Module.Free L (L ⊗[B] M) := free_at_geometricallyIntegralGenericPrime A B P
  exact (Module.mem_freeLocus_iff_tensor (M := M) Q L).mpr hf

/--
概要：基礎環上平坦な有限表示加群の拡大素点での階数は局所定数。
方針：拡大素点への連続写像を自由 locus へ持ち上げ、既存の階数定理を引き戻す。
規約：KST §5、Stacks 0810・0811、代数の実際の分裂表示の下で述べる。
使われ方：一般階数が一定となる開集合で係数中心を選ぶ。
-/
theorem isLocallyConstant_genericRank :
    IsLocallyConstant (fun P : PrimeSpectrum A =>
      Module.rankAtStalk M (geometricallyIntegralGenericPrime A B P)) := by
  let g : PrimeSpectrum A → Module.freeLocus B M := fun P =>
    ⟨geometricallyIntegralGenericPrime A B P,
      genericPrime_mem_freeLocus A B (M := M) P⟩
  have hg : Continuous g :=
    (continuous_geometricallyIntegralGenericPrime A B e p hpe).subtype_mk _
  change IsLocallyConstant ((fun x : Module.freeLocus B M => Module.rankAtStalk M x.1) ∘ g)
  exact (Module.isLocallyConstant_rankAtStalk_freeLocus (R := B) (M := M)).comp_continuous hg

/--
概要：実際のテンソル局所化で計算した一般階数も局所定数。
方針：stalk の階数とテンソル局所化の有限階数の標準等式を使う。
規約：KST §5、Stacks 0810・0811、代数の実際の分裂表示の下で述べる。
使われ方：小行列式の次数を一定にする開集合への制限。
-/
theorem isLocallyConstant_genericTensorRank :
    IsLocallyConstant (fun P : PrimeSpectrum A =>
      let L := Localization.AtPrime (geometricallyIntegralGenericPrime A B P).asIdeal
      Module.finrank L (L ⊗[B] M)) := by
  simpa only [Module.rankAtStalk_eq_finrank_tensorProduct] using
    isLocallyConstant_genericRank A B e p hpe (M := M)

/--
概要：一般階数が指定した値になる素点の集合は開かつ閉。
方針：一般階数の局所定数性から各ファイバーの開閉性を得る。
規約：KST §5、Stacks 0810・0811、分裂表示を入力する補助段階。
使われ方：一定階数の部分へ分けて係数中心を作る。
-/
theorem isClopen_genericRank_fiber (r : ℕ) :
    IsClopen {P : PrimeSpectrum A |
      Module.rankAtStalk M (geometricallyIntegralGenericPrime A B P) = r} :=
  (isLocallyConstant_genericRank A B e p hpe (M := M)).isClopen_fiber r

/--
概要：一般階数の値は有限個しかない。
方針：素スペクトルのコンパクト性と階数の局所定数性を使う。
規約：KST §5、Stacks 0810・0811、分裂表示を入力する補助段階。
使われ方：一定階数の開閉分解を有限個の中心にまとめる。
-/
theorem genericRank_range_finite :
    (Set.range (fun P : PrimeSpectrum A =>
      Module.rankAtStalk M (geometricallyIntegralGenericPrime A B P))).Finite :=
  (isLocallyConstant_genericRank A B e p hpe (M := M)).range_finite

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
