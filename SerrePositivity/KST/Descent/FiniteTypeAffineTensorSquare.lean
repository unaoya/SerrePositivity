module

public import SerrePositivity.KST.Descent.AffineTensorSquare
public import Mathlib.CategoryTheory.Limits.Over

/-!
# 有限型の圏内の同変なアフィン底変換

## 概要
テンソル積モデルの Cartesian 性を、同じ S 上の前層の定義域内へ持ち上げる。

## 方針
指定二射影を Over の射に包み、忘却関手の極限の反映を使う。

## 規約
元の前層の評価対象と指定作用を保持する。Tot による降下の接続は別工程。

## 使われ方
論文 補題 3.2 を Čech 計算で扱う際の各底変換の同変な正方形。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T] [Algebra.FiniteType A B] [Algebra.FiniteType A T]
variable (a : Spec (.of A) ⟶ S) [LocallyOfFiniteType a] [QuasiCompact a]

/-- 概要：テンソル積を固定した S 上の有限型対象にする（論文 補題 3.2）。
方針：左因子 B への構造射を元の S への構造射と合成する。
規約：底変換後も前層の定義域は同じ。
使われ方：同変な Cartesian 正方形の左上の頂点。 -/
noncomputable def affineTensorObject : FiniteTypeSchemes S :=
  @affineAlgebraOverObject S B (B ⊗[A] T) _ _ _ _
    (affineAlgebraOverObject (T := B) a).obj.hom
    (affineAlgebraOverObject (T := B) a).property.1
    (affineAlgebraOverObject (T := B) a).property.2

/-- 概要：有限型の圏内の左因子への射影（論文 補題 3.2）。
方針：既存の係数射影をそのまま使う。
規約：左因子 B への射影を第一射影とする。
使われ方：底変換後の指定降下比較。 -/
noncomputable def affineTensorFst : affineTensorObject (B := B) (T := T) a ⟶
    affineAlgebraOverObject (T := B) a :=
  @affineAlgebraOverProjection S B (B ⊗[A] T) _ _ _ _
    (affineAlgebraOverObject (T := B) a).obj.hom
    (affineAlgebraOverObject (T := B) a).property.1
    (affineAlgebraOverObject (T := B) a).property.2

/-- 概要：有限型の圏内の右因子への射影（論文 補題 3.2）。
方針：実際のテンソル積の正方形の可換性で S 上の射に持ち上げる。
規約：右因子への環の包含の Spec を使う。
使われ方：元の射との底変換正方形。 -/
noncomputable def affineTensorSnd : affineTensorObject (B := B) (T := T) a ⟶
    affineAlgebraOverObject (T := T) a :=
  ObjectProperty.homMk (Over.homMk (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T).toRingHom)) (by
      change Spec.map _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap A T)) ≫ a) =
        Spec.map _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ a)
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k ↦ k ≫ a) (tensorSpecSquare_comm A B T).symm).trans
          (Category.assoc _ _ _))))

/-- 概要：指定されたアフィン底変換の正方形の可換性（論文 補題 3.2）。
方針：忘却後に Spec の二射影の可換性を使う。
規約：有限型の圏内の射の等式。
使われ方：前層を適用する Cartesian 正方形。 -/
theorem affineTensorSquare_comm :
    affineTensorFst (T := T) a ≫ affineAlgebraOverProjection a =
      affineTensorSnd (B := B) a ≫ affineAlgebraOverProjection a := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact tensorSpecSquare_comm A B T

/-- 概要：元の前層の定義域内の実際のアフィン底変換（論文 補題 3.2）。
方針：Over と充満部分圏の忘却による極限の反映を使う。
規約：指定された四辺そのものが有限型の圏で引き戻しを成す。
使われ方：Čech の各段に対して前層を適用する際の普遍性。 -/
theorem affineTensorSquare_isPullback :
    IsPullback (affineTensorFst (T := T) a) (affineTensorSnd (B := B) a)
      (affineAlgebraOverProjection a) (affineAlgebraOverProjection a) := by
  let F := ObjectProperty.ι
    (fun X : Over S ↦ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom) ⋙ Over.forget S
  exact (tensorSpecSquare_isPullback A B T).of_map F (affineTensorSquare_comm a)

/-- 概要：指定された環の持ち上げから実際の底変換の切断（論文 補題 3.2）。
方針：テンソル積の分裂を Spec の切断にして固定した S 上へ持ち上げる。
規約：切断は有限型の圏内にあり、前層は変更しない。
使われ方：Čech の各底変換での分裂データ。 -/
noncomputable def affineTensorSection (φ : T →ₐ[A] B) :
    affineAlgebraOverObject (T := B) a ⟶ affineTensorObject (B := B) (T := T) a :=
  @affineSplitSection S B (B ⊗[A] T) _ _ _ _
    (affineAlgebraOverObject (T := B) a).obj.hom
    (affineAlgebraOverObject (T := B) a).property.1
    (affineAlgebraOverObject (T := B) a).property.2 (tensorBaseChangeRetraction φ)

/-- 概要：底変換の第一射影と指定切断の分裂恒等式（論文 補題 3.2）。
方針：忘却してテンソル積の分裂の Spec の恒等式を適用する。
規約：有限型の圏内の指定された射そのものの等式。
使われ方：実際の Čech nerve の余分な退化の構成。 -/
theorem affineTensorSection_identity (φ : T →ₐ[A] B) :
    affineTensorSection a φ ≫ affineTensorFst a = 𝟙 (affineAlgebraOverObject (T := B) a) := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact affineSplitSection_raw_identity (tensorBaseChangeRetraction φ)

variable {G : Type u} [Group G] [MulSemiringAction G T] [SMulCommClass G A T]

/-- 概要：実際のアフィン底変換の有限型対象の指定作用（論文 補題 3.2）。
方針：左因子の構造射の有限型性を取り出して既存の作用を適用する。
規約：左因子は固定して右因子だけを動かす。
使われ方：Čech の各段の全次数降下。 -/
noncomputable def affineTensorAction : G →* Aut (affineTensorObject (B := B) (T := T) a) :=
  @affineAlgebraOverAction S B (B ⊗[A] T) _ _ _ _ G _ _ _
    (affineAlgebraOverObject (T := B) a).obj.hom
    (affineAlgebraOverObject (T := B) a).property.1
    (affineAlgebraOverObject (T := B) a).property.2

/-- 概要：指定第一射影は基底上の作用を持つ（論文 補題 3.2）。
方針：忘却後に係数保存の Spec の等式を適用する。
規約：有限型の圏内の指定射影そのもの。
使われ方：全次数の不変部分への指定比較。 -/
theorem affineTensorAction_over_base (g : G) :
    (affineTensorAction (B := B) (T := T) a g).asIso.hom ≫ affineTensorFst a =
      affineTensorFst a := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact specAction_over_base g

/-- 概要：有限型の圏内の右射影は元の作用と同変（論文 補題 3.2）。
方針：忘却後に指定された環からの二つの作用を比較する。
規約：左因子は固定、右因子には元の作用を適用する。
使われ方：Čech 底変換の不変部分の比較。 -/
theorem affineTensorSnd_equivariant (g : G) :
    (affineTensorAction (B := B) (T := T) a g).asIso.hom ≫ affineTensorSnd a =
      affineTensorSnd a ≫ (affineAlgebraOverAction (T := T) a g).asIso.hom := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact tensorSpecSquare_right_equivariant g

/-- 概要：実際の有限型アフィン底変換の第一射影の全次数降下（論文 補題 3.2）。
方針：同じ S 上のテンソル積モデルの分裂を使った降下を指定第一射影へ適用する。
規約：自然な blowup 列・有限積保存・冪零不変性は明示した条件のまま。
使われ方：Čech の各段への局所比較の入力。 -/
theorem NaturalBlowupSequences.affineTensorFst_piDescent [IsNoetherian S]
    {Coefficient : Type w}
    {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}
    (data : NaturalBlowupSequences L) [Nilinvariant S L]
    [∀ H n, PreservesFiniteProducts (L H n)] [Finite G] [IsSeparated a]
    (φ : T →ₐ[A] B) (transitive : IsGeometricallyTransitive A T G)
    (d : ℕ) (bound : topologicalKrullDim (Spec (.of B)) ≤ d) :
    L.PiDescent (affineTensorFst (B := B) (T := T) a)
      (affineTensorAction (G := G) a) (affineTensorAction_over_base a) := by
  have : IsSeparated (affineAlgebraOverObject (T := B) a).obj.hom :=
    inferInstanceAs (IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ a))
  exact @NaturalBlowupSequences.affine_baseChange_piDescent A B T _ _ _ _ _ _ G _ _ _
    S _ Coefficient L data _ _ _
    (affineAlgebraOverObject (T := B) a).obj.hom
    (affineAlgebraOverObject (T := B) a).property.1
    (affineAlgebraOverObject (T := B) a).property.2 this φ transitive d bound

end SerrePositivity.KST.Descent
