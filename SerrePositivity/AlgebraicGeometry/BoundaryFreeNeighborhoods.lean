module

public import SerrePositivity.AlgebraicGeometry.GenericBoundaryFreeNeighborhood

/-!
概要：KST §5、Stacks 0810 の基礎環を覆う純変換の自由な基本開近傍。
方針：元の基底変更加群の純変換について、自由化元と共通階数を述べる。
規約：存在定理を仮定する構造体は導入せず、結論だけを述語にまとめる。
使われ方：実際の blowup チャート上の自由化元の存在を一定階数の中心から得る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：純変換が基礎環の各素点上のある基本開で共通階数の自由加群となる条件。
方針：基底変更多元環の拡大素イデアルに属さない自由化元を実際に量化する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、定義に幾何学的整性や Noether 性は不要。
使われ方：有限生成中心のチャートで得る結論の固定環による記述。
-/
def BoundaryPureFreeNeighborhoods (A B C : Type u) (M : Type*)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [AddCommGroup M] [Module B M] (f : C) (r : ℕ) : Prop :=
  let D := C ⊗[A] B
  letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let G := modulePureTransform (algebraMap C D f) (D ⊗[B] M)
  ∀ P : PrimeSpectrum C,
    ∃ g ∉ P.asIdeal.map (algebraMap C D),
      Module.Free (Localization.Away g) (LocalizedModule.Away g G) ∧
        Module.finrank (Localization.Away g) (LocalizedModule.Away g G) = r

/--
概要：一般点で自由な有限加群の境界純変換には基礎環を覆う自由な基本開近傍が存在する。
方針：各拡大素点で得た同じ階数の自由基底を基本開へ降ろす。
規約：KST §5、Stacks 0810, Lemma 38.30.2、元の加群の有限性は代数上に課す。
使われ方：一般点の自由化中心を原典の自由化元による結論へ接続する。
-/
theorem boundaryPureFreeNeighborhoods_of_genericBoundaryPureFree
    (A B C : Type u) (M : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing C] [Module.Flat A B]
    [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [AddCommGroup M] [Module B M] [Module.Finite B M]
    (f : C) (r : ℕ) (hGF : GenericBoundaryPureFree A B C M f r) :
    BoundaryPureFreeNeighborhoods A B C M f r :=
  fun P => exists_away_free_finrank_of_genericBoundaryPureFree A B C M f r hGF P

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
