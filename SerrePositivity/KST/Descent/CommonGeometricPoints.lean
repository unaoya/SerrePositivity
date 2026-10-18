module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# 同じ基底点にある二点の幾何点への持ち上げ

## 概要
二つのスキームの同じ基底点の上にある点を、共通の代数閉体からの射で表す。

## 方針
引き戻しの点を選び、その剰余体の代数閉包からの射を二つの射影へ合成する。

## 規約
幾何点の間の射の等式を主張せず、基底への合成の等式と点の像を保持する。

## 使われ方
論文 定理 3.1 の幾何ファイバーの推移性から基礎点のファイバーの推移性への移行。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：同じ基底点の上の二点は共通の代数閉体上の幾何点で表せる（論文 定理 3.1）。
方針：引き戻しの点の剰余体を代数閉包へ拡大し、両射影と合成する。
規約：二つの基底への合成はスキームの射として等しく、指定した二点を像に持つ。
使われ方：幾何ファイバーの推移性を通常の点のファイバーへ降ろす。 -/
theorem exists_common_geometric_points {X Y B : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (x : X) (y : Y) (same_base : f x = g y) :
    ∃ (Ω : Type u) (field : Field Ω), letI := field
      IsAlgClosed Ω ∧ ∃ (a : Spec (.of Ω) ⟶ X) (b : Spec (.of Ω) ⟶ Y),
        a ≫ f = b ≫ g ∧ ∃ t : Spec (.of Ω), a t = x ∧ b t = y := by
  classical
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y same_base
  let P := pullback f g
  let K := P.residueField z
  let Ω := AlgebraicClosure K
  let e : Spec (.of Ω) ⟶ P :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ P.fromSpecResidueField z
  refine ⟨Ω, inferInstance, inferInstance, e ≫ pullback.fst f g,
    e ≫ pullback.snd f g, ?_, default, ?_, ?_⟩
  · simp only [Category.assoc, pullback.condition]
  · change pullback.fst f g (e default) = x
    have he : e default = z := by
      exact P.fromSpecResidueField_apply z _
    exact (congrArg (pullback.fst f g) he).trans hz₁
  · change pullback.snd f g (e default) = y
    have he : e default = z := by
      exact P.fromSpecResidueField_apply z _
    exact (congrArg (pullback.snd f g) he).trans hz₂

end SerrePositivity.KST.Descent
