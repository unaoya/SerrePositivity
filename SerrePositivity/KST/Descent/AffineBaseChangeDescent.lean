module

public import SerrePositivity.KST.Descent.AffineSplitDescent
public import SerrePositivity.KST.Descent.GeometricBaseChange

/-!
# 分裂するアフィン底変換の降下

## 概要
T →ₐ[A] B があるとき、B ⊗_A T → B の分裂を構成し、全次数降下を証明する。

## 方針
係数拡大での幾何的推移性を使い、固定した S 上の元の前層 L に適用する。

## 規約
テンソル積は左因子 B 上の代数。実際の Čech nerve との同変比較は別工程である。

## 使われ方
論文 補題 3.2 の Čech 計算による置換と、定理 3.1 の切断を作る底変換。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace TensorProduct

namespace SerrePositivity.KST.Descent

variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T]

/-- 概要：環の射 T → B から底変換の分裂を構成する（論文 補題 3.2）。
方針：左因子は恒等写像、右因子は指定された代数射とする。
規約：分裂は B 代数射であり、左因子の係数を保存する。
使われ方：Spec B 上の実際の切断。 -/
noncomputable def tensorBaseChangeRetraction (φ : T →ₐ[A] B) : B ⊗[A] T →ₐ[B] B :=
  Algebra.TensorProduct.lift (AlgHom.id B B) φ (fun _ _ ↦ Commute.all _ _)

/-- 概要：底変換の分裂の純テンソル上の公式（論文 補題 3.2）。
方針：テンソル積の普遍性の評価公式を使う。
規約：左因子を掛け、右因子には指定代数射を適用する。
使われ方：Čech の対角切断との比較。 -/
@[simp] theorem tensorBaseChangeRetraction_tmul (φ : T →ₐ[A] B) (b : B) (t : T) :
    tensorBaseChangeRetraction φ (b ⊗ₜ[A] t) = b * φ t := by
  simp [tensorBaseChangeRetraction]

variable [Algebra.FiniteType A T] {G : Type u} [Group G] [MulSemiringAction G T]
  [SMulCommClass G A T] {S : Scheme.{u}}

/-- 概要：分裂する底変換の指定射影は全次数降下を満たす（論文 補題 3.2・定理 3.1）。
方針：幾何的推移性を係数拡大し、構成した分裂から切断つき降下を適用する。
規約：元の S 上の L を使い、自然な列・有限積保存・冪零不変性を入力する。
使われ方：Čech 各段に現れるテンソル積モデルの指定比較。 -/
theorem NaturalBlowupSequences.affine_baseChange_piDescent [IsNoetherian S]
    {Coefficient : Type w}
    {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}
    (data : NaturalBlowupSequences L) [Nilinvariant S L]
    [∀ H n, PreservesFiniteProducts (L H n)] [Finite G]
    (b : Spec (.of B) ⟶ S) [LocallyOfFiniteType b] [QuasiCompact b] [IsSeparated b]
    (φ : T →ₐ[A] B) (transitive : IsGeometricallyTransitive A T G)
    (d : ℕ) (bound : topologicalKrullDim (Spec (.of B)) ≤ d) :
    L.PiDescent (affineAlgebraOverProjection (T := B ⊗[A] T) b)
      (affineAlgebraOverAction (G := G) b) (affineAlgebraOverAction_over_base b) := by
  exact data.affine_split_piDescent b (tensorBaseChangeRetraction φ)
    (geometricTransitivity_baseChange transitive) d bound

/-- 概要：自己底変換したアフィン射の全次数降下（論文 補題 3.2）。
方針：T → T の恒等代数射から乗法による分裂を構成する。
規約：T ⊗_A T の右因子だけに群が作用し、左因子 T は固定する。
使われ方：元の射を自身で引き戻す Čech の最初の段階。 -/
theorem NaturalBlowupSequences.affine_selfBaseChange_piDescent [IsNoetherian S]
    {Coefficient : Type w}
    {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}
    (data : NaturalBlowupSequences L) [Nilinvariant S L]
    [∀ H n, PreservesFiniteProducts (L H n)] [Finite G]
    (b : Spec (.of T) ⟶ S) [LocallyOfFiniteType b] [QuasiCompact b] [IsSeparated b]
    (transitive : IsGeometricallyTransitive A T G)
    (d : ℕ) (bound : topologicalKrullDim (Spec (.of T)) ≤ d) :
    L.PiDescent (affineAlgebraOverProjection (T := T ⊗[A] T) b)
      (affineAlgebraOverAction (G := G) b) (affineAlgebraOverAction_over_base b) := by
  exact data.affine_baseChange_piDescent b (AlgHom.id A T) transitive d bound

end SerrePositivity.KST.Descent
