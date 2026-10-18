module

public import SerrePositivity.KST.Descent.AffinePresentation
public import SerrePositivity.KST.Descent.FiniteFlatFreeCover
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# 元のアフィン有限忠実平坦射の表示と自由自明化

## 概要
元のスキーム射の有限性・平坦性・有限表示性・全射性を実際の表示環準同型へ移す。

## 方針
Spec の標準同型で移した射を検査し、有限表示平坦代数の有限自由な基本開自明化を適用する。

## 規約
表示環の代数構造は元の射から選ぶ。自由性や正の局所 rank は追加の仮定にしない。

## 使われ方
論文 補題 3.2 の局所 transfer と、補題 3.3 の実際の有限忠実平坦細分への適用。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped TensorProduct

namespace SerrePositivity.KST.Descent

variable {R B : Type u} [CommRing R] [CommRing B] {X Y : Scheme.{u}}
  (f : X ⟶ Y) (eX : Spec (.of B) ≅ X) (eY : Spec (.of R) ≅ Y)

/-- 概要：元の平坦射の実際の表示環準同型は平坦（論文 補題 3.2）。
方針：同型の合成の平坦性を Spec の平坦射判定へ移す。
規約：元の射と同じ表示環準同型を用いる。
使われ方：実際の有限平坦射の有限自由自明化の平坦性入力。 -/
theorem affinePresentationMap_flat [AlgebraicGeometry.Flat f] :
    (affinePresentationMap f eX eY).Flat := by
  have h : AlgebraicGeometry.Flat
      (Spec.map (CommRingCat.ofHom (affinePresentationMap f eX eY))) := by
    rw [affinePresentationMap_spec]
    infer_instance
  exact AlgebraicGeometry.Flat.SpecMap_iff.mp h

/-- 概要：元の有限表示射の実際の表示環準同型は有限表示（論文 補題 3.2）。
方針：同型の合成の有限表示性を Spec の判定へ移す。
規約：有限型性へ弱めない。
使われ方：stalk から基本開まで自由基底を広げる有限表示性の供給。 -/
theorem affinePresentationMap_finitePresentation [LocallyOfFinitePresentation f] :
    (affinePresentationMap f eX eY).FinitePresentation := by
  have h : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (affinePresentationMap f eX eY))) := by
    rw [affinePresentationMap_spec]
    infer_instance
  exact (LocallyOfFinitePresentation.SpecMap_iff _).mp h

/-- 概要：元の全射の実際の表示環準同型の Spec も全射（論文 補題 3.2）。
方針：元の射と両端の同型の合成について全射性を使う。
規約：環準同型そのものの全射性とは区別する。
使われ方：局所の有限自由基底の本数が正であることの入力。 -/
theorem affinePresentationMap_spec_surjective [Surjective f] :
    Surjective (Spec.map (CommRingCat.ofHom (affinePresentationMap f eX eY))) := by
  rw [affinePresentationMap_spec]
  infer_instance

/-- 概要：実際の有限忠実平坦有限表示射の表示は有限自由な基本開自明化を持つ（補題 3.2）。
方針：元の射の性質を選んだ代数構造へ移し、証明済みの正の有限基底被覆を適用する。
規約：同じ表示環準同型の toAlgebra を使い、元の環と全切断環を同一視しない。
使われ方：アフィン開制限した実際の被覆を transfer の局所 rank 公式へ渡す。 -/
theorem exists_affinePresentation_positive_basis_cover [IsFinite f]
    [AlgebraicGeometry.Flat f] [Surjective f] [LocallyOfFinitePresentation f] :
    letI : Algebra R B := (affinePresentationMap f eX eY).toAlgebra
    ∃ s : Finset R, Ideal.span (s : Set R) = ⊤ ∧
      ∀ r ∈ s, ∃ rank : ℕ, 0 < rank ∧ Nonempty
        (Basis (Fin rank) (Localization.Away r) (Localization.Away r ⊗[R] B)) := by
  let : Algebra R B := (affinePresentationMap f eX eY).toAlgebra
  have : Module.Finite R B := affinePresentationMap_moduleFinite f eX eY
  have : Module.Flat R B := affinePresentationMap_flat f eX eY
  have : Algebra.FinitePresentation R B := affinePresentationMap_finitePresentation f eX eY
  have : Module.FinitePresentation R B :=
    Module.FinitePresentation.of_finite_of_finitePresentation R B
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    affinePresentationMap_spec_surjective f eX eY
  exact exists_positive_basis_tensor_cover R B

end SerrePositivity.KST.Descent
