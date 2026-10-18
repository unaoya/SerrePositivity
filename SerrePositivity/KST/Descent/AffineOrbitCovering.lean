module

public import SerrePositivity.KST.Descent.SpecAction
public import SerrePositivity.KST.Descent.FiniteTypeAction
public import SerrePositivity.KST.Descent.TranslatedSections

/-!
# 有限型アフィン対象の移動切断による被覆

## 概要
既存の環論的な幾何的推移性から、実際の有限型対象の移動切断の被覆を構成する。

## 方針
Spec の作用を有限型の圏へ持ち上げ、証明済みの点の推移性を切断の被覆判定に適用する。

## 規約
切断の存在は明示的に入力する。有限忠実平坦な Čech 還元による切断の構成は別工程。

## 使われ方
論文 補題 3.2・定理 3.1 の切断を持つ場合の軌道正方形への被覆条件。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable (A T : Type u) [CommRing A] [CommRing T] [Algebra A T] [Algebra.FiniteType A T]

/-- 概要：Spec A をその上の有限型対象とする（論文 §3）。
方針：構造射を恒等射とする。
規約：前層 L の定義域内の基底対象。
使われ方：アフィン射の有限型の圏内の終域。 -/
noncomputable def affineBaseObject : FiniteTypeSchemes (Spec (.of A)) :=
  ⟨Over.mk (𝟙 (Spec (.of A))),
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of A)))),
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of A))))⟩

/-- 概要：有限型 A 代数を Spec A 上の有限型対象とする（論文 §3）。
方針：algebraMap の Spec を構造射とする。
規約：代数の有限型性を仮定し、有限性は要求しない。
使われ方：環論的な幾何的推移性を幾何的な軌道構成へ入力する。 -/
noncomputable def affineAlgebraObject : FiniteTypeSchemes (Spec (.of A)) :=
  ⟨Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A T))),
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance),
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap A T))))⟩

/-- 概要：アフィン構造射を有限型の圏内の射にする（論文 §3）。
方針：基底の恒等構造射への射として包む。
規約：スキームの射は元の algebraMap の Spec そのもの。
使われ方：切断の恒等式と軌道の PiDescent の指定射。 -/
noncomputable def affineAlgebraProjection : affineAlgebraObject A T ⟶ affineBaseObject A :=
  ObjectProperty.homMk (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A T))))

variable {G : Type u} [Group G] [MulSemiringAction G T] [SMulCommClass G A T]

/-- 概要：環の作用を有限型アフィン対象の作用へ持ち上げる（論文 定理 3.1）。
方針：Spec の左作用が構造射を保つことを使う。
規約：元の Spec の各自己同型を変更しない。
使われ方：重複を除いた移動切断の添字と、実際の軌道正方形。 -/
noncomputable def affineAlgebraAction : G →* Aut (affineAlgebraObject A T) :=
  finiteTypeActionOfSchemeAction (affineAlgebraObject A T) specAction specAction_over_base

/-- 概要：有限型アフィン対象の作用は指定射の基底上にある（論文 (3.7)）。
方針：忘却して Spec の構造射の保存を適用する。
規約：有限型の圏内の射の等式を結論する。
使われ方：移動切断の切断性と PiDescent の不変性の条件。 -/
theorem affineAlgebraAction_over_base (g : G) :
    (affineAlgebraAction A T g).asIso.hom ≫ affineAlgebraProjection A T =
      affineAlgebraProjection A T := by
  apply ObjectProperty.hom_ext
  apply (Over.forget (Spec (.of A))).map_injective
  exact specAction_over_base g

/-- 概要：幾何的推移性から相異なる移動切断の像が全体を覆う（論文 定理 3.1）。
方針：Spec の点のファイバー上の推移性を、実際の切断族の被覆判定へ入力する。
規約：既存の IsGeometricallyTransitive をそのまま仮定し、被覆条件を別に仮定しない。
使われ方：軌道正方形とその中心の帰納段階へ供給する被覆。 -/
theorem affine_translatedSection_covering (transitive : IsGeometricallyTransitive A T G)
    (s : affineBaseObject A ⟶ affineAlgebraObject A T)
    (hs : s ≫ affineAlgebraProjection A T = 𝟙 (affineBaseObject A)) :
    ⋃ t : TranslatedSectionIndex (affineAlgebraAction (G := G) A T) s,
      Set.range t.val.hom.left = Set.univ := by
  apply translatedSection_covering (affineAlgebraProjection A T) s hs (affineAlgebraAction A T)
  intro x y hxy
  exact specAction_transitive_on_fibers transitive x y hxy

end SerrePositivity.KST.Descent
