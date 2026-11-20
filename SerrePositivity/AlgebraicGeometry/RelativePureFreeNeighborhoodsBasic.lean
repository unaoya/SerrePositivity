module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.RelativePureFreeNeighborhoods
public import SerrePositivity.AlgebraicGeometry.BoundaryFreeNeighborhoods
public import SerrePositivity.AlgebraicGeometry.FreeNeighborhoodStalk
public import SerrePositivity.AlgebraicGeometry.PureTransformCongr

/-!
概要：KST §5、Stacks 0810・0811 の相対自由化基本開の比較と一般点での判定。
方針：定義の照合、純変換と局所化の実際の同型、一般点の自由基底の降下を使う。
規約：線形同型による保存には環や加群の有限性は不要。
使われ方：構成済みの自由化中心を押し出しの任意の実現へ渡す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：標準テンソル積の自由化基本開の述語は、実際の代数に対する相対述語と一致する。
方針：二つの定義を展開して同じ量化と同じ純変換を照合する。
規約：KST §5、Stacks 0810・0811、代数の右因子の作用を明示する。
使われ方：既存の中心の結論を押し出しモデルの保存定理へ渡す。
-/
theorem boundaryPureFreeNeighborhoods_iff_relative
    (A B C : Type u) (M : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [AddCommGroup M] [Module B M] (f : C) (r : ℕ) :
    BoundaryPureFreeNeighborhoods A B C M f r ↔
      let D := C ⊗[A] B
      letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
      RelativePureFreeNeighborhoods C D (D ⊗[B] M) f r := Iff.rfl

/--
概要：相対自由化基本開の存在は代数上の実際の線形同型で保存される。
方針：純変換の同型を各自由化元で局所化し、自由性と有限階数を運ぶ。
規約：KST §5、Stacks 0810・0811、有限性や Noether 性は不要。
使われ方：二段の基底変更加群を同じ代数上の別表示へ移す。
-/
theorem RelativePureFreeNeighborhoods.congr
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    {f : R} {r : ℕ} (h : RelativePureFreeNeighborhoods R S M f r) (E : M ≃ₗ[S] N) :
    RelativePureFreeNeighborhoods R S N f r := by
  intro P
  obtain ⟨g, hg, hfree, hr⟩ := h P
  let : Module.Free (Localization.Away g)
      (LocalizedModule.Away g (modulePureTransform (algebraMap R S f) M)) := hfree
  let E₀ := modulePureTransformCongr (algebraMap R S f) E
  let E₁ := IsLocalizedModule.mapEquiv (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) (modulePureTransform (algebraMap R S f) M))
    (LocalizedModule.mkLinearMap (Submonoid.powers g) (modulePureTransform (algebraMap R S f) N))
    (Localization.Away g) E₀
  exact ⟨g, hg, Module.Free.of_equiv E₁, E₁.finrank_eq.symm.trans hr⟩

/--
概要：二段の基底変更加群の相対自由化基本開を、取消同型による一段の表示へ移せる。
方針：実際の代数上のテンソル取消同型に線形同型による保存を適用する。
規約：KST §5、Stacks 0810・0811、環や加群の有限性は不要。
使われ方：押し出し保存の結論の加群を元の基礎環からの一段の基底変更として読む。
-/
theorem RelativePureFreeNeighborhoods.cancelBaseChange
    {A B C D M : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A D] [Algebra B D] [IsScalarTower A B D] [Algebra C D]
    [AddCommGroup M] [Module A M] {f : C} {r : ℕ}
    (h : RelativePureFreeNeighborhoods C D (D ⊗[B] (B ⊗[A] M)) f r) :
    RelativePureFreeNeighborhoods C D (D ⊗[A] M) f r :=
  h.congr (TensorProduct.AlgebraTensorModule.cancelBaseChange A B D D M)

/--
概要：相対自由化基本開の存在は全拡大一般点での自由性と同じ局所階数という条件と同値。
方針：基本開から自由性と階数を戻し、逆向きは Noether 有限表示加群の自由基底を基本開へ降ろす。
規約：KST §5、Stacks 0810・0811、実分裂はこの同値には不要。
使われ方：構成済みの中心を任意の押し出しでの一般点保存定理へ接続する。
-/
theorem relativePureFreeNeighborhoods_iff_genericPureFree
    (R S : Type u) (M : Type*) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Module.Flat R S] [Algebra.FinitePresentation R S]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [AddCommGroup M] [Module S M] [Module.Finite S M] (f : R) (r : ℕ) :
    RelativePureFreeNeighborhoods R S M f r ↔
      ∀ P : PrimeSpectrum R,
        let Q := geometricallyIntegralGenericPrime R S P
        let G := modulePureTransform (algebraMap R S f) M
        Q ∈ Module.freeLocus S G ∧ Module.rankAtStalk G Q = r := by
  constructor
  · intro h P
    obtain ⟨g, hg, hfree, hr⟩ := h P
    exact freeLocus_and_rankAtStalk_of_away_free
      (geometricallyIntegralGenericPrime R S P) g hg r hfree hr
  · intro h
    let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
    let G := modulePureTransform (algebraMap R S f) M
    let : Module.FinitePresentation S G := Module.finitePresentation_of_finite S G
    intro P
    obtain ⟨g, hg, hfree, hr⟩ := exists_away_free_finrank_of_mem_freeLocus
      (geometricallyIntegralGenericPrime R S P) (h P).1
    exact ⟨g, hg, hfree, hr.trans (h P).2⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
