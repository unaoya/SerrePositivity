module

public import SerrePositivity.KST.Descent.Axioms
public import SerrePositivity.KST.Descent.ClosedDimension
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# 閉中心の被約閉部分スキームとしての実現

## 概要
任意の閉部分集合に消滅イデアル層で被約閉部分スキームの構造を入れる。
基底上有限型の対象に対しては、中心も同じ有限型スキームの圏の対象になる。

## 方針
各アフィン開集合で消滅イデアルによる商が被約であることを証明し、開被覆で貼り合わせる。
台との同相を使って、閉部分集合上の次元帰納を実際のスキームへ移す。

## 規約
任意の閉部分スキームが被約であるとは主張しない。
ここでは消滅イデアル層による被約構造を選んでいる。

## 使われ方
論文 補題 3.3 の閉中心と、定理 3.1 の一致場所の和 Z を実際の閉中心として扱う。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

variable {X : Scheme.{u}}

/-- 概要：閉部分集合に入れる被約閉部分スキームの構造（論文 §3 の閉中心）。
方針：閉部分集合の消滅イデアル層に対応する閉部分スキームを取る。
規約：閉部分集合を単なる型として終わらせず、構造層を持つスキームにする。
使われ方：一致場所の和と平坦化の中心の被約構造。 -/
noncomputable def reducedClosedSubscheme (Z : Closeds X) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal Z).subscheme

/-- 概要：被約閉中心から元のスキームへの包含（論文 §3）。
方針：消滅イデアル層の閉部分スキームの包含を使う。
規約：点集合の包含だけではなく、スキームの射。
使われ方：抽象 blowup 正方形の閉中心の射。 -/
noncomputable def reducedClosedInclusion (Z : Closeds X) : reducedClosedSubscheme Z ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι

/-- 概要：選んだ閉中心の包含は閉埋め込み（論文 §3）。
方針：イデアル層からの閉部分スキームの包含の性質を使う。
規約：有限型性や固有性に使う実際の射の性質。
使われ方：有限型の圏への包含と抽象 blowup の条件。 -/
instance reducedClosedInclusion_isClosedImmersion (Z : Closeds X) :
    IsClosedImmersion (reducedClosedInclusion Z) := by
  change IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  infer_instance

/-- 概要：選んだ閉中心の台は元の閉部分集合そのもの（論文 §3）。
方針：消滅イデアル層の台と閉部分スキームの像の公式を使う。
規約：台を更に閉包していない。
使われ方：一致場所の中心の台と補開集合を特定する。 -/
theorem range_reducedClosedInclusion (Z : Closeds X) :
    Set.range (reducedClosedInclusion Z) = (Z : Set X) := by
  change Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- 概要：消滅イデアル層による閉部分スキームは被約（論文 §3 の被約中心）。
方針：アフィン被覆で、消滅イデアルは根基イデアルなので商環が被約であることを使う。
規約：元のスキームの被約性は不要。
使われ方：閉中心に対する被約な基底上の帰納。 -/
instance reducedClosedSubscheme_isReduced (Z : Closeds X) :
    IsReduced (reducedClosedSubscheme Z) := by
  let J := Scheme.IdealSheafData.vanishingIdeal Z
  have charts (U : X.affineOpens) : IsReduced (J.subschemeCover.openCover.X U) := by
    have : _root_.IsReduced (Γ(X, U) ⧸ J.ideal U) := by
      apply (Ideal.isRadical_iff_quotient_reduced _).mp
      change (PrimeSpectrum.vanishingIdeal _).IsRadical
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    change IsReduced (Spec (CommRingCat.of (Γ(X, U) ⧸ J.ideal U)))
    infer_instance
  exact @IsReduced.of_openCover J.subscheme J.subschemeCover.openCover charts

/-- 概要：被約閉中心とその台との同相（論文 §3）。
方針：閉埋め込みの像への同相を、消滅イデアル層の台の同定と合成する。
規約：次元を計算する際の基礎位相空間の同相。
使われ方：真閉部分集合の次元低下を実際の閉中心へ移す。 -/
noncomputable def reducedClosedHomeo (Z : Closeds X) : reducedClosedSubscheme Z ≃ₜ Z :=
  (reducedClosedInclusion Z).isClosedEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_reducedClosedInclusion Z))

/-- 概要：被約閉中心の Krull 次元は台の次元に一致（論文 §3）。
方針：閉中心と台の同相による次元不変性を使う。
規約：空の中心は次元 ⊥ のまま扱う。
使われ方：軌道正方形の中心上の帰納。 -/
theorem reducedClosedSubscheme_dimension (Z : Closeds X) :
    topologicalKrullDim (reducedClosedSubscheme Z) = topologicalKrullDim Z :=
  IsHomeomorph.topologicalKrullDim_eq _ (reducedClosedHomeo Z).isHomeomorph

/-- 概要：真閉中心の実際のスキームの次元は有限上界 d より小さい（論文 §3）。
方針：台の次元低下と、閉中心と台の同相を組み合わせる。
規約：既約な元のスキームと有限な上界を明示する。
使われ方：補題 3.3・定理 3.1 のスキームとしての次元帰納。 -/
theorem reducedClosedSubscheme_dimension_lt_bound [IrreducibleSpace X]
    (Z : Closeds X) (proper : (Z : Set X) ≠ Set.univ)
    (d : ℕ) (bound : topologicalKrullDim X ≤ d) :
    topologicalKrullDim (reducedClosedSubscheme Z) < d := by
  rw [reducedClosedSubscheme_dimension]
  exact topologicalKrullDim_properClosed_lt_bound Z Z.isClosed proper d bound

/-- 概要：有限型 S スキームの被約閉中心も有限型 S スキーム（論文 §3）。
方針：閉埋め込みの局所有限型性・準コンパクト性を構造射に合成する。
規約：元の対象の有限型性を明示的に使い、Noether 性や有限次元性は推論しない。
使われ方：L の定義域である有限型スキームの圏の中で中心に評価する。 -/
noncomputable def reducedClosedAsFiniteType {S : Scheme.{u}} (X : FiniteTypeSchemes S)
    (Z : Closeds X.obj.left) : FiniteTypeSchemes S := by
  have : LocallyOfFiniteType X.obj.hom := X.property.1
  have : QuasiCompact X.obj.hom := X.property.2
  exact ⟨Over.mk (reducedClosedInclusion Z ≫ X.obj.hom),
    locallyOfFiniteType_comp _ _, quasiCompact_comp _ _⟩

/-- 概要：有限型の圏内の被約閉中心は被約（論文 定理 3.1）。
方針：消滅イデアル層から構成した被約閉部分スキームの性質を使う。
規約：元の対象 X の被約性は不要。
使われ方：中心上の切断を引き戻しの始域の被約化へ持ち上げる。 -/
instance reducedClosedAsFiniteType_isReduced {S : Scheme.{u}}
    (X : FiniteTypeSchemes S) (Z : Closeds X.obj.left) :
    IsReduced (reducedClosedAsFiniteType X Z).obj.left :=
  inferInstanceAs (IsReduced (reducedClosedSubscheme Z))

/-- 概要：有限型スキームの圏における閉中心の包含（論文 §3）。
方針：構造射との可換式を持つ `Over` の射を充満部分圏へ入れる。
規約：基底 S を保つ射。
使われ方：閉中心を含む前層の正方形の指定制限写像。 -/
noncomputable def reducedClosedAsFiniteTypeInclusion {S : Scheme.{u}} (X : FiniteTypeSchemes S)
    (Z : Closeds X.obj.left) : reducedClosedAsFiniteType X Z ⟶ X :=
  ObjectProperty.homMk (Over.homMk (reducedClosedInclusion Z))

/-- 概要：有限型の圏内の被約閉中心の包含は閉埋め込み（論文 §3）。
方針：忘却後の射を消滅イデアル層の包含として判定する。
規約：基底 S 上有限型という包みを保ったまま instance を供給する。
使われ方：中心の引き戻しと群作用の構成。 -/
instance reducedClosedAsFiniteTypeInclusion_isClosedImmersion {S : Scheme.{u}}
    (X : FiniteTypeSchemes S) (Z : Closeds X.obj.left) :
    IsClosedImmersion (reducedClosedAsFiniteTypeInclusion X Z).hom.left :=
  reducedClosedInclusion_isClosedImmersion Z

end SerrePositivity.KST.Descent
