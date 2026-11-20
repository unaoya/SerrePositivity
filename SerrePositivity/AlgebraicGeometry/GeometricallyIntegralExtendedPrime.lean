module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.QuotientPullback
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.FiniteStability

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の幾何学的整な代数での拡大素イデアル。
方針：整 Noether な商の Spec への基底変更を、拡大イデアルの商の Spec と同定する。
規約：基礎環は Noether、射は平坦・有限表示・幾何学的整とする。
使われ方：係数 blowup 後の特別な局所環の素性の入力。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

/--
概要：幾何学的整なアフィン射は任意の係数環へのテンソル基底変更後も幾何学的整。
方針：テンソル積の Spec とファイバー積の実同型を使い、同型に関する不変性と基底変更安定性を適用する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、この段階には Noether 性や平坦性は不要。
使われ方：blowup チャートの係数環に対する拡大素性を導く。
-/
theorem geometricallyIntegral_tensorProjection
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))] :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B)))) := by
  have : MorphismProperty.RespectsIso @GeometricallyIntegral := by
    rw [GeometricallyIntegral.eq_geometrically]
    infer_instance
  rw [← pullbackSpecIso_inv_fst' A C B,
    MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral]
  infer_instance

/--
概要：Noether 基礎環上の平坦・有限表示・幾何学的整な代数では、素イデアルの拡大は素。
方針：素イデアルによる整 Noether な商へ基底変更し、その整性を商の Spec の同型で移す。
規約：KST §5、Stacks 0810, Lemma 38.30.2、幾何学的整性は Spec の射の標準条件。
使われ方：基礎環の素点に対応する代数の特別な局所環を構成する。
-/
theorem ideal_map_isPrime_of_geometricallyIntegral
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    (P : Ideal A) [P.IsPrime] : (P.map (algebraMap A B)).IsPrime := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))
  have : Flat f := (Flat.SpecMap_iff).mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : LocallyOfFinitePresentation f :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have : IsIntegral (pullback f g) := inferInstance
  have : IsIntegral (Spec (.of (B ⧸ P.map (algebraMap A B)))) :=
    IsIntegral.of_isIso (specQuotientPullbackIso A B P).hom
  exact (Ideal.Quotient.isDomain_iff_prime (P.map (algebraMap A B))).mp
    ((affine_isIntegral_iff (.of (B ⧸ P.map (algebraMap A B)))).mp inferInstance)

/--
概要：幾何学的整な平坦有限表示代数を Noether 係数環へ基底変更すると、同係数環の素イデアルの拡大は素。
方針：テンソル射の幾何学的整性と平坦性・有限表示性の保存から拡大素性を適用する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、Noether 条件は基底変更先に課す。
使われ方：実 blowup チャート上の特別な局所環の素性の存在証明。
-/
theorem ideal_map_tensor_isPrime_of_geometricallyIntegral
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [IsNoetherianRing C] [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    (P : Ideal C) [P.IsPrime] : (P.map (algebraMap C (C ⊗[A] B))).IsPrime := by
  have : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B)))) :=
    geometricallyIntegral_tensorProjection A B C
  exact ideal_map_isPrime_of_geometricallyIntegral C (C ⊗[A] B) P

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
