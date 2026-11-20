module

public import SerrePositivity.AlgebraicGeometry.RelativePureFreeNeighborhoodsBasic
public import SerrePositivity.AlgebraicGeometry.PureFreeStalkBaseChange

/-!
概要：KST §5、Stacks 0810・0811 の代数同型による相対自由化基本開の移送。
方針：同型による拡大一般点の保存と一素点での純変換の基底変更保存を使う。
規約：実際の同型を代数作用に選び、移送先の加群はその基底変更とする。
使われ方：第二段のテンソル代数を取消代数同型で一段の表示へ移す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/--
概要：相対自由化基本開の存在は、正則な境界を保つ代数同型による基底変更で同じ階数のまま移送できる。
方針：同型で縮約する拡大一般点を照合し、旧一般点の自由性を新純変換へ運んで基本開へ降ろす。
規約：KST §5、Stacks 0810・0811、実分裂は不要で両代数の平坦有限表示性・幾何学的整性を使う。
使われ方：第二段の自由化中心を元の基礎環上の一段のテンソル代数で読む。
-/
theorem relativePureFreeNeighborhoods_baseChange_of_algEquiv
    (R S T : Type u) (M : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [IsNoetherianRing R]
    [Module.Flat R S] [Algebra.FinitePresentation R S]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [Module.Flat R T] [Algebra.FinitePresentation R T]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R T)))]
    [AddCommGroup M] [Module S M] [Module.Finite S M]
    (E : S ≃ₐ[R] T) (f : R) (r : ℕ) (hN : RelativePureFreeNeighborhoods R S M f r)
    (hf : IsRegular (algebraMap R T f)) :
    letI : Algebra S T := E.toRingHom.toAlgebra
    RelativePureFreeNeighborhoods R T (T ⊗[S] M) f r := by
  let : Algebra S T := E.toRingHom.toAlgebra
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have hfree := (relativePureFreeNeighborhoods_iff_genericPureFree R S M f r).mp hN
  apply (relativePureFreeNeighborhoods_iff_genericPureFree R T (T ⊗[S] M) f r).mpr
  intro P
  let Q := geometricallyIntegralGenericPrime R T P
  have hC : E.toRingHom.comp (algebraMap R S) = algebraMap R T := by
    ext x
    exact E.commutes x
  have hQ : Q.comap (algebraMap S T) = geometricallyIntegralGenericPrime R S P := by
    apply PrimeSpectrum.ext
    change (P.asIdeal.map (algebraMap R T)).comap E.toRingHom =
      P.asIdeal.map (algebraMap R S)
    rw [← hC, ← Ideal.map_map, Ideal.comap_map_of_bijective E.toRingHom E.bijective]
  have hsource : Q.comap (algebraMap S T) ∈
      Module.freeLocus S (modulePureTransform (algebraMap R S f) M) ∧
      Module.rankAtStalk (modulePureTransform (algebraMap R S f) M)
        (Q.comap (algebraMap S T)) = r := by
    rw [hQ]
    exact hfree P
  have hscalar : algebraMap S T (algebraMap R S f) = algebraMap R T f := E.commutes f
  have hd : IsRegular (algebraMap T (Localization.AtPrime Q.asIdeal)
      (algebraMap S T (algebraMap R S f))) := by
    rw [hscalar]
    apply isRegular_iff_mem_nonZeroDivisors.mpr
    exact IsLocalization.nonZeroDivisors_le_comap
      (S := Localization.AtPrime Q.asIdeal) Q.asIdeal.primeCompl
      (isRegular_iff_mem_nonZeroDivisors.mp hf)
  have h := pureTransform_freeLocus_rankAtStalk_baseChange
    (M := M) (algebraMap R S f) r Q hsource hd
  rwa [hscalar] at h

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
