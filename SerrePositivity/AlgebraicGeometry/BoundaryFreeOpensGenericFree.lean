module

public import SerrePositivity.AlgebraicGeometry.BoundaryFreeOpenPullbacks

/-!
概要：KST §5、Stacks 0811 の階数を指定しない自由化基本開と一般点自由性の同値。
方針：基本開から素点の自由性を取り出し、逆向きは有限表示の自由基底を基本開へ降ろす。
規約：共通階数は要求せず、基礎素点の拡大イデアルが素イデアルであることを使う。
使われ方：基礎環の基本開ごとの自由化を大域で照合する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：基礎を覆う自由化基本開の存在は、純変換の全拡大一般点での自由性と同値。
方針：各一般点の自由基底と自由化基本開を有限表示性により相互に移す。
規約：KST §5、Stacks 0811、基礎環は Noether、元の加群は代数上有限。
使われ方：階数の異なる成分を含めた自由化の開局所性を判定する。
-/
theorem boundaryPureFreeOpens_iff_genericPureFree
    (A B C : Type u) (M : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing C] [Module.Flat A B]
    [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [AddCommGroup M] [Module B M] [Module.Finite B M] (f : C) :
    BoundaryPureFreeOpens A B C M f ↔
      let D := C ⊗[A] B
      letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
      letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
        geometricallyIntegral_tensorProjection A B C
      ∀ P : PrimeSpectrum C,
        geometricallyIntegralGenericPrime C D P ∈
          Module.freeLocus D (modulePureTransform (algebraMap C D f) (D ⊗[B] M)) := by
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  let G := modulePureTransform (algebraMap C D f) (D ⊗[B] M)
  let : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing C D
  let : Module.FinitePresentation D G := Module.finitePresentation_of_finite D G
  dsimp only
  constructor
  · intro h P
    obtain ⟨g, hg, hfree⟩ := h P
    exact (freeLocus_and_rankAtStalk_of_away_free
      (geometricallyIntegralGenericPrime C D P) g hg _ hfree rfl).1
  · intro h P
    obtain ⟨g, hg, hfree, _⟩ := exists_away_free_finrank_of_mem_freeLocus _ (h P)
    exact ⟨g, hg, hfree⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
