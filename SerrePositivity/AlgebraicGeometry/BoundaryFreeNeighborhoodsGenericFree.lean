module

public import SerrePositivity.AlgebraicGeometry.BoundaryFreeNeighborhoods
public import SerrePositivity.AlgebraicGeometry.FreeNeighborhoodStalk

/-!
概要：KST §5、Stacks 0810・0811 の自由化基本開から一般点での純変換の自由性への接続。
方針：各拡大素点を含む自由化元を選び、その点での自由性と局所階数を取り出す。
規約：元の加群の有限性は代数上に課す。
使われ方：既存の自由化中心の結論を追加基底変更保存の入力へ渡す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：各基礎素点上の共通階数の自由化基本開は、純変換の全拡大一般点での自由性と同じ局所階数を与える。
方針：各素点の自由化元を選び、基本開から元の素点へ自由性と階数を戻す。
規約：KST §5、Stacks 0810・0811、実分裂はこの逆向きの判定には不要。
使われ方：選んだ中心による自由化の結果をさらに細分した後も保存する準備。
-/
theorem genericPureTransformFree_of_boundaryPureFreeNeighborhoods
    (A B C : Type u) (M : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing C] [Module.Flat A B]
    [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [AddCommGroup M] [Module B M] [Module.Finite B M]
    (f : C) (r : ℕ) (hN : BoundaryPureFreeNeighborhoods A B C M f r) :
    let D := C ⊗[A] B
    letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
    letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
      geometricallyIntegral_tensorProjection A B C
    ∀ P : PrimeSpectrum C,
      let Q := geometricallyIntegralGenericPrime C D P
      let G := modulePureTransform (algebraMap C D f) (D ⊗[B] M)
      Q ∈ Module.freeLocus D G ∧ Module.rankAtStalk G Q = r := by
  dsimp only
  let D := C ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  intro P
  obtain ⟨g, hg, hfree, hr⟩ := hN P
  exact freeLocus_and_rankAtStalk_of_away_free
    (geometricallyIntegralGenericPrime C D P) g hg r hfree hr

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
