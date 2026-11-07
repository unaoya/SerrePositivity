module

public import SerrePositivity.AlgebraicGeometry.GeometricallyIntegralProjectivity
public import SerrePositivity.AlgebraicGeometry.SplitAlgebraFreeOpenBlowup

/-!
概要：幾何学的整なファイバーを持つ平坦有限型代数上の有限加群の自由化。
方針：05FS で基底上の射影性を得て、既存の二段の自由化中心とその支配を適用する。
規約：Noether アフィン基底と正則な主境界における Stacks 0811 の形。
使われ方：純変換の自由部分を取り出し、余核のファイバーの台の次元を下げる。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：幾何学的整なファイバーを持つ平坦有限型代数上の有限加群について、
境界外で基底上平坦なら、純変換が基底を覆う自由化基本開を持つ blowup 中心が存在する。
方針：Noether 基底上の有限表示性と 05FS の射影性を自由化中心の構成に渡す。
規約：境界は一つの正則元で与える。自由化基本開は正則な境界を持つ
Noether アフィン試験対象への引き戻しについても得られる。
使われ方：Stacks 0811 から 0815 の台の次元による帰納へ進むための入力。
-/
theorem exists_fg_center_boundaryFreeOpenPullbacks_of_geometricallyIntegral
    {A : CommRingCat.{u}} (B : Type u) [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Module.Flat A B] [Algebra.FiniteType A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M : Type v} [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M]
    (f : A) (hf : IsRegular f)
    [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[A] M)] :
    ∃ K : Ideal A, K.FG ∧ affineCenterComplement K = PrimeSpectrum.basicOpen f ∧
      HasBoundaryFreeOpenPullbacks B (affineBlowupπ K) f M := by
  let : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp
    inferInstance
  let : Module.Projective A B := projective_of_flat_finiteType_geometricallyIntegral A B
  exact exists_fg_center_boundaryFreeOpenPullbacks_of_projective B f hf

end SerrePositivity.AlgebraicGeometry
