module

public import SerrePositivity.AlgebraicGeometry.BoundaryFlatBaseChange
public import SerrePositivity.AlgebraicGeometry.FiberDimensionReduction
public import SerrePositivity.AlgebraicGeometry.GeometricallyIntegralFiberRegularity
public import SerrePositivity.AlgebraicGeometry.GeometricallyIntegralProjectivity
public import SerrePositivity.AlgebraicGeometry.PureFreeStalkBaseChange
public import SerrePositivity.AlgebraicGeometry.PureTransformCongr
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import SerrePositivity.AlgebraicGeometry.SmoothFiberKrullDimension
public import SerrePositivity.AlgebraicGeometry.UniformFreeOpenNeighborhood

/-!
概要：自由化主開が各ファイバーにある滑らかな正規化先で、余核の台の次元帰納を適用する。
方針：基底を主近傍に縮めて一つの自由化主開を使い、余核を平坦化する。
規約：滑らかさと幾何学的整性は正規化先に課す。
使われ方：Stacks 0815 の最初のブローアップの各チャート上で局所中心を作る。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

/--
概要：より小さいファイバー台を持つ有限加群を、境界外を保つアフィン中心で平坦化できる条件。
方針：各 Noether 基底と有限型代数に対して、余核の帰納に使う形で量化する。
規約：台の次元に一を足して上限と比較するので、上限零では零加群だけを許す。
使われ方：Stacks 0815 の次元帰納の仮定。
-/
def HasAffineFlatPureCentersBelow (n : ℕ) : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (B N : Type u)
    [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N] [Module.Finite B N]
    (a : R), IsRegular a →
    Module.Flat (Localization.Away a) (Localization.Away a ⊗[R] N) →
    (∀ p : PrimeSpectrum R, let F := B ⊗[R] p.asIdeal.ResidueField
      Module.supportDim F (F ⊗[B] N) + 1 ≤ (n : WithBot ℕ∞)) →
    ∃ I : Ideal R, I.FG ∧ PrimeSpectrum.basicOpen a ≤ affineCenterComplement I ∧
      HasFlatPurePullbacks (affineBlowupπ I) a N

/--
概要：係数環上の線形同型で、純変換の引き戻し平坦性を移す。
方針：各試験環で線形同型を基底変更し、純変換の商に誘導する。
規約：境界元は両側で共通。
使われ方：代数上の二段テンソル積から基礎環上の一段の底変換へ戻す。
-/
theorem HasFlatPurePullbacks.congrModule {R : CommRingCat.{u}} {X : Scheme.{u}}
    {p : X ⟶ Spec R} {a : R} {M : Type v} {N : Type w}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (h : HasFlatPurePullbacks p a M) (e : M ≃ₗ[R] N) :
    HasFlatPurePullbacks p a N := by
  intro A j
  dsimp only
  intro ha
  let φ := pureTransformCoefficientMap p j
  let : Algebra R A := φ.toAlgebra
  let : Module.Flat A (modulePureTransform (φ a) (A ⊗[R] M)) := h A j ha
  exact Module.Flat.of_linearEquiv (modulePureTransformCongr (φ a) (e.baseChange R A _ _)).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
-- 主開の局所化とその剰余体への二重の底変換のインスタンスを合成する。
/--
概要：各ファイバーと交わる自由化主開を持つ場合、基底の各点の主近傍で、次元が小さい場合から平坦化中心を得る。
方針：指定点での自由化元を一つ選び、主近傍の全ファイバーで非零となるようにして余核を使う。
規約：幾何学的整で相対次元が一定の滑らかな代数を使う。
使われ方：自由化ブローアップ上で局所中心を作り、基底の主開被覆で貼り合わせる。
-/
theorem exists_basicOpen_flatPure_center_of_smaller_fibers
    {R : CommRingCat.{u}} {B N : Type u} [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Module.Flat R B] [Algebra.FiniteType R B]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N] [Module.Finite B N]
    (n : ℕ) [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    (a : R) (ha : IsRegular a) [Module.Flat (Localization.Away a) (Localization.Away a ⊗[R] N)]
    (hrec : HasAffineFlatPureCentersBelow.{u} n) (p : PrimeSpectrum R) (b : B)
    (hb : b ∉ p.asIdeal.map (algebraMap R B))
    [Module.Free (Localization.Away b) (Localization.Away b ⊗[B] N)] :
    ∃ c ∉ p.asIdeal, let A := CommRingCat.of (Localization.Away c)
      letI : Algebra R A := inferInstanceAs (Algebra R (Localization.Away c))
      ∃ J : Ideal A, J.FG ∧ PrimeSpectrum.basicOpen (algebraMap R A a) ≤
        affineCenterComplement J ∧
        HasFlatPurePullbacks (affineBlowupπ J) (algebraMap R A a) (A ⊗[R] N) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : IsDomain (p.asIdeal.Fiber B) :=
    isDomain_tensor_of_geometricallyIntegral R B p.asIdeal.ResidueField
  obtain ⟨c, hc, hfree, hnonzero⟩ :=
    exists_uniform_freeOpen_over_basicOpen (N := N) f.isOpenMap p b hb
  let A := CommRingCat.of (Localization.Away c)
  let : Algebra R A := inferInstanceAs (Algebra R (Localization.Away c))
  let D := A ⊗[R] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let P := D ⊗[B] N
  let d := algebraMap B D b
  let e := algebraMap R A a
  let g := Spec.map (CommRingCat.ofHom (algebraMap A D))
  let : IsNoetherianRing A := inferInstanceAs (IsNoetherianRing (Localization.Away c))
  let : GeometricallyIntegral g := geometricallyIntegral_tensorProjection R B A
  let : SmoothOfRelativeDimension n g :=
    MorphismProperty.of_isPullback (isPullback_specTensor R B A) inferInstance
  let : Module.Projective A D := projective_of_flat_finiteType_geometricallyIntegral A D
  let : Module.Free (Localization.Away d) (Localization.Away d ⊗[D] P) := hfree
  let : Module.Flat (Localization.Away e) (Localization.Away e ⊗[A] P) :=
    flat_tensorAlgebra_away_of_boundary_flat R A N B a
  have hDom (q : PrimeSpectrum A) : IsDomain (D ⊗[A] q.asIdeal.ResidueField) :=
    letI : IsDomain (q.asIdeal.ResidueField ⊗[A] D) :=
      isDomain_tensor_of_geometricallyIntegral A D q.asIdeal.ResidueField
    (Algebra.TensorProduct.comm A D q.asIdeal.ResidueField).toRingEquiv.toMulEquiv.isDomain _
  have hnotNilpotent : ¬ IsNilpotent d := by
    obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range (Localization.Away c) c).ge hc
    let : IsDomain (D ⊗[A] q.asIdeal.ResidueField) := hDom q
    intro hn
    exact hnonzero q (isNilpotent_iff_eq_zero.mp (hn.map (algebraMap D _)))
  let : Nontrivial (Localization.Away d) :=
    (IsLocalization.toLocalizationMap (.powers d) (Localization.Away d)).nontrivial hnotNilpotent
  obtain ⟨J, hJ, hJa, hflat⟩ :=
    exists_affine_flatPure_center_of_smaller_fiber_cokernels (R := A) (N := P) e d hDom hnonzero n
      (ringKrullDim_fiber_le_of_smoothOfRelativeDimension_spec n) (fun Q _ _ _ _ _ hdim hQ =>
        hrec A D Q e (algebraMap_isRegular_of_flat R A a ha) hQ hdim)
  let E := tensorAlgebraBaseChangeEquiv R B A N
  exact ⟨c, hc, J, hJ, hJa, hflat.congrModule E⟩

end SerrePositivity.AlgebraicGeometry
