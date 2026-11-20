module

public import SerrePositivity.AlgebraicGeometry.BoundaryLocallyConstantCharts
public import SerrePositivity.AlgebraicGeometry.SplitGenericPrimeContinuity
public import SerrePositivity.AlgebraicGeometry.SplitAlgebraTensorCoefficients
public import SerrePositivity.AlgebraicGeometry.TensorAlgebraBaseChangeFlat

/-!
概要：KST §5、Stacks 0811 の境界外一般階数の局所定数性と実チャートによる分離。
方針：境界外へ実分裂と相対平坦性を移し、一般階数の開閉部分を一段の中心で分離する。
規約：元の一般階数の引き戻しがチャートの境界外で一定となることを述べる。
使われ方：一定一般階数の係数中心の定理をチャートごとに適用する準備。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
  [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
  (M : Type*) [AddCommGroup M] [Module B M]

/--
概要：境界外へ基底変更した有限型代数上の加群の一般階数。
方針：境界外の基礎素点を拡大して局所化し、テンソル局所化の有限階数を取る。
規約：KST §5、Stacks 0811, Lemma 38.30.3、定義に加群の平坦性や有限性は不要。
使われ方：一般階数の有限開閉分割を実際の blowup 中心へ渡す。
-/
def boundaryGenericRank (f : A) : PrimeSpectrum (Localization.Away f) → ℕ :=
  let F := Localization.Away f
  let D := F ⊗[A] B
  letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
  letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap F D))) :=
    geometricallyIntegral_tensorProjection A B F
  fun P =>
    let L := Localization.AtPrime (geometricallyIntegralGenericPrime F D P).asIdeal
    Module.finrank L (L ⊗[D] (D ⊗[B] M))

variable [Module A M] [IsScalarTower A B M] [Module.Finite B M]

/--
概要：実分裂を持つ代数上の有限加群が境界外で相対平坦なら、境界外一般階数は局所定数。
方針：実分裂のテンソル基底変更と平坦性の取消同型を使い、一般階数の局所定数性へ還元する。
規約：KST §5、Stacks 0811, Lemma 38.30.3、元の環上での加群の平坦性は要求しない。
使われ方：境界外一般階数の有限開閉部分を選ぶ。
-/
theorem isLocallyConstant_boundaryGenericRank {ι : Type*}
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (f : A) [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[A] M)] :
    IsLocallyConstant (boundaryGenericRank A B M f) := by
  let F := Localization.Away f
  let D := F ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap F D))) :=
    geometricallyIntegral_tensorProjection A B F
  let : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing F D
  let : Module.FinitePresentation D (D ⊗[B] M) := Module.finitePresentation_of_finite D _
  let : Module.Flat F (D ⊗[B] M) := tensorAlgebraBaseChange_flat A B F M
  let e' := splitAlgebraTensorEmbedding (C := F) e
  let p' := splitAlgebraTensorRetraction (C := F) p
  have hs : p'.comp e' = LinearMap.id := splitAlgebraTensorRetraction_comp_embedding e p hpe
  exact isLocallyConstant_genericTensorRank F D e' p' hs (M := D ⊗[B] M)

/--
概要：境界外一般階数を各標準チャートの境界外で一定にする有限生成中心が存在する。
方針：実際の一般階数の局所定数性を、有限開閉分割を分離する中心の定理へ渡す。
規約：KST §5、Stacks 0811, Lemma 38.30.3、元の階数の引き戻しを結論に保持する。
使われ方：一定一般階数を仮定する中心の定理へ進むための実際の最初の blowup。
-/
theorem exists_fg_center_constant_boundaryGenericRank {ι : Type*}
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (f : A) (hf : IsRegular f)
    [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[A] M)] :
    ∃ (I : Ideal A) (a : Set.range (boundaryGenericRank A B M f) → I),
      I.FG ∧ affineCenterComplement I = PrimeSpectrum.basicOpen f ∧
      (⨆ i, affineBlowupChart I (a i)) = ⊤ ∧
      Pairwise (fun i j => Disjoint (affineBlowupChart I (a i)) (affineBlowupChart I (a j))) ∧
      ∀ i (P : PrimeSpectrum (Localization.Away (chartBaseMap I (a i) f))),
        boundaryGenericRank A B M f
          (PrimeSpectrum.comap (Localization.awayMap (chartBaseMap I (a i)) f) P) = i.val :=
  exists_fg_center_constant_on_boundary_charts f hf (boundaryGenericRank A B M f)
    (isLocallyConstant_boundaryGenericRank A B M e p hpe f)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
