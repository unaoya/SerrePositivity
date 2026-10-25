module
public import SerrePositivity.KST.SConstruction.TriangulatedKZeroEquiv

/-!
概要：指定された実 K 射の零次単射性を、同じ完全関手の三角圏 K₀ 単射性と同値にする。
方針：既存の対象類を保つ比較同型の自然性で二つの単射性を輸送する。
規約：K₀ 単射性そのものは未証明であり、充満忠実性だけから結論しない。
使われ方：Thomason 共終性の零次部分を、一般の dense 三角圏の議論と接続する境界。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet Spectra

/-- 概要：同じ完全関手について実 K 射の零次単射性と三角圏 K₀ 単射性は同値。
方針：元の比較同型と自然性で単射性を両方向へ移す。
規約：共終性の証明や零次全射性を仮定しない。
使われ方：一般の dense 包含についての K₀ 証明の消費。 -/
theorem kSpectrumMap_zero_injective_iff {X Y : StableModel.{u}} (f : X ⟶ Y) :
    Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0) ↔
      Function.Injective (triangulatedKZeroSourceMap f) := by
  let eX := (triangulatedKZeroEquiv X).toEquiv.trans Additive.toMul
  let eY := (triangulatedKZeroEquiv Y).toEquiv.trans Additive.toMul
  have he (a : TriangulatedK0 (hoFunctor.obj X.carrier)) :
      eY (triangulatedKZeroSourceMap f a) =
        OmegaSpectrum.homotopyMap (kSpectrumMap f) 0 (eX a) :=
    congrArg Additive.toMul (triangulatedKZeroEquiv_naturality f a)
  constructor
  · intro h a b hab
    apply eX.injective
    apply h
    rw [← he, ← he, hab]
  · intro h a b hab
    obtain ⟨a, rfl⟩ := eX.surjective a
    obtain ⟨b, rfl⟩ := eX.surjective b
    apply congrArg eX
    apply h
    apply eY.injective
    rw [he, he, hab]

end SerrePositivity.KST.SConstruction.Cofinality
