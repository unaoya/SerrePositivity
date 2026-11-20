module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.BoundaryFreeNeighborhoodsSingleBaseChange
public import SerrePositivity.AlgebraicGeometry.PureTransformPullbacks

/-!
概要：KST §5、Stacks 0811 の基礎を覆う自由化基本開をアフィン試験対象への引き戻しで述べる。
方針：各試験環の各素点で自由化元を量化し、既証の基底変更保存を適用する。
規約：階数は成分で変わり得るため共通階数を要求せず、中心の存在を仮定に含めない。
使われ方：異なる階数を持つ第二段チャートの自由化を一つのスキーム上で扱う。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

/--
概要：純変換が基礎環の各素点上のある基本開で自由となる条件。
方針：拡大素イデアルに属さない自由化元を各素点で選ぶ。
規約：KST §5、Stacks 0811、共通自由階数は要求しない。
使われ方：一般階数の異なる開閉成分を一つの結論にまとめる。
-/
def BoundaryPureFreeOpens (A B C : Type u) (M : Type*)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [AddCommGroup M] [Module B M] (f : C) : Prop :=
  let D := C ⊗[A] B
  letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let G := modulePureTransform (algebraMap C D f) (D ⊗[B] M)
  ∀ P : PrimeSpectrum C,
    ∃ g ∉ P.asIdeal.map (algebraMap C D),
      Module.Free (Localization.Away g) (LocalizedModule.Away g G)

/--
概要：共通階数の自由化基本開から階数を指定しない自由化基本開を得る。
方針：各素点で同じ自由化元を使い、階数等式を忘れる。
規約：KST §5、Stacks 0811、有限性と Noether 性は不要。
使われ方：チャートごとの階数を持つ存在定理を大域の性質へ接続する。
-/
theorem BoundaryPureFreeNeighborhoods.freeOpens
    {A B C : Type u} {M : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [AddCommGroup M] [Module B M]
    {f : C} {r : ℕ} (h : BoundaryPureFreeNeighborhoods A B C M f r) :
    BoundaryPureFreeOpens A B C M f := by
  intro P
  obtain ⟨g, hg, hfree, _⟩ := h P
  exact ⟨g, hg, hfree⟩

/--
概要：正則な境界を持つ全 Noether アフィン試験対象で基礎を覆う自由化基本開が存在する性質。
方針：射から得る実際の係数写像で純変換と自由化元を量化する。
規約：KST §5、Stacks 0811、試験環上の共通階数と平坦化中心の存在は要求しない。
使われ方：二段自由化の被覆を支配射に沿って引き戻す。
-/
def HasBoundaryFreeOpenPullbacks {A : CommRingCat.{u}} (B : Type u)
    [CommRing B] [Algebra A B] {X : Scheme.{u}}
    (p : X ⟶ Spec A) (f : A) (M : Type v) [AddCommGroup M] [Module B M] : Prop :=
  ∀ (C : CommRingCat.{u}) [IsNoetherianRing C] (j : Spec C ⟶ X),
    let φ := pureTransformCoefficientMap p j
    letI : Algebra A C := φ.toAlgebra
    IsRegular (φ f) → BoundaryPureFreeOpens A B C M (φ f)

/--
概要：全 Noether アフィン試験対象での自由化基本開の存在は任意の前合成で保存される。
方針：試験射を合成し、係数写像の合成公式で元の性質を適用する。
規約：KST §5、Stacks 0811、射の始域への追加仮定は不要。
使われ方：元の基底の一つの blowup から二段自由化対象への支配射に適用する。
-/
theorem HasBoundaryFreeOpenPullbacks.comp {A : CommRingCat.{u}} {B : Type u}
    [CommRing B] [Algebra A B] {X Y : Scheme.{u}} {p : X ⟶ Spec A}
    {f : A} {M : Type v} [AddCommGroup M] [Module B M]
    (hp : HasBoundaryFreeOpenPullbacks B p f M) (q : Y ⟶ X) :
    HasBoundaryFreeOpenPullbacks B (q ≫ p) f M := by
  intro C hC j
  let P (φ : A →+* C) : Prop :=
    letI : Algebra A C := φ.toAlgebra
    IsRegular (φ f) → BoundaryPureFreeOpens A B C M (φ f)
  exact (congrArg P (pureTransformCoefficientMap_comp p q j)).mpr (hp C (j ≫ q))

/--
概要：固定階数の自由化基本開を持つ Noether アフィン係数環は、全 Noether アフィン試験対象で自由化基本開を持つ。
方針：各試験射の環準同型を取り、追加の正則境界基底変更による保存を適用する。
規約：KST §5、Stacks 0811、元の代数の実分裂を入力する。
使われ方：構成した第二段の各チャートの自由化を任意の支配射で使える形へ移す。
-/
theorem hasBoundaryFreeOpenPullbacks_spec_of_neighborhoods
    {A : CommRingCat.{u}} (B C : Type u) [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing C]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι : Type*} [AddCommGroup M] [Module B M] [Module.Finite B M]
    (e : B →ₗ[A] (ι →₀ A)) (s : (ι →₀ A) →ₗ[A] B) (hse : s.comp e = LinearMap.id)
    (f : A) (r : ℕ) (hN : BoundaryPureFreeNeighborhoods A B C M (algebraMap A C f) r) :
    HasBoundaryFreeOpenPullbacks B (Spec.map (CommRingCat.ofHom (algebraMap A C))) f M := by
  intro E hE j
  let χ : C →+* E := (Spec.preimage j).hom
  let : Algebra C E := χ.toAlgebra
  let φ : A →+* E := χ.comp (algebraMap A C)
  let : Algebra A E := φ.toAlgebra
  let : @IsScalarTower A C E (inferInstance : Algebra A C).toSMul
      (inferInstance : Algebra C E).toSMul (inferInstance : Algebra A E).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := A) (S := C) (A := E) rfl
  let P (θ : A →+* E) : Prop :=
    letI : Algebra A E := θ.toAlgebra
    IsRegular (θ f) → BoundaryPureFreeOpens A B E M (θ f)
  have hφ : P φ := by
    intro hf
    exact (boundaryPureFreeNeighborhoods_baseChange A B C E M e s hse
      (algebraMap A C f) r hN hf).freeOpens
  exact (congrArg P (pureTransformCoefficientMap_spec
    (CommRingCat.ofHom (algebraMap A C)) j)).mpr hφ

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
