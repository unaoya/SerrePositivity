module

public import SerrePositivity.EInfinity.BarrattEccles.CAlg
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantAlgebraMappingClasses
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization
public import SerrePositivity.EInfinity.SimplicialLocalization.KanComponents

/-!
# 実際の DK Hom と元の E 代数の Map^h の連結成分の同値

概要：任意の可換環上の同じ cofibrant E 代数の DK Hom と Map^h の π₀ を同定する。
方針：元の augmentation の同値、Hom の ULift の同値、既存の Map^h の同値を合成する。
規約：同じ対象・射・置換・Kan Hom を保持する。高次の弱同値は後続。
使われ方：E2b の高次比較の元の射での零次の正規化。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Opposite
open SerrePositivity.EInfinity.SimplicialLocalization

variable (A : Type u) [CommRing A]

/-- 概要：元の cofibrant E 代数を同じ Hom の DK 宇宙へ移す（Dwyer–Kan）。
方針：元の ULiftHom.up の対象写像を使う。
規約：対象も置換も選び直さない。
使われ方：元の Map^h の対象と DK Hom の対象の照合。 -/
def cofibrantAlgebraDKObject (X : CofibrantAlgebra A) :
    (cofibrantAlgebraRelativeCategory A).category :=
  (ULiftHom.up.{u, u + 1, u + 1} (C := CofibrantAlgebra A)).obj X

/-- 概要：元の DK Hom の π₀ は同じ cofibrant 代数の元の Map^h の π₀（Dwyer–Kan）。
方針：同じ augmentation・Hom の ULift・既存の Map^h の比較を合成する。
規約：高次の単体集合の比較へ置き換えない。
使われ方：E2b の高次比較の零次の同定。 -/
def cofibrantAlgebraDKPiZeroEquiv (X Y : CofibrantAlgebra A) :
    SSet.π₀ (localizationHom (cofibrantAlgebraRelativeCategory A)
      (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y)) ≃
        SSet.π₀ (((cofibrantAlgebraMappingSpace A).obj (op X)).obj Y) :=
  (localizationHomPiZeroEquiv (cofibrantAlgebraRelativeCategory A) _ _).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.homEquiv (cofibrantAlgebraWeakEquivalences A) _ _).trans
      (cofibrantAlgebraMappingSpacePiZeroEquiv A X Y).symm)

/-- 概要：同じ DK の生成射の類は元の同じ Map^h の射の類（Dwyer–Kan）。
方針：両側の Q への正規化と Hom の ULift の同じ射の計算を使う。
規約：元の cofibrant 代数射と元の零単体の類を保持する。
使われ方：高次比較が保持するべき元の射の正規化。 -/
lemma cofibrantAlgebraDKPiZeroEquiv_class {X Y : CofibrantAlgebra A} (f : X ⟶ Y) :
    cofibrantAlgebraDKPiZeroEquiv A X Y
        (localizationArrowClass (cofibrantAlgebraRelativeCategory A)
          ((ULiftHom.up.{u, u + 1, u + 1} (C := CofibrantAlgebra A)).map f)) =
      mappingSpaceClass A ((cofibrantAlgebraInclusion A).map f) := by
  apply (cofibrantAlgebraMappingSpacePiZeroEquiv A X Y).injective
  change (cofibrantAlgebraMappingSpacePiZeroEquiv A X Y)
    ((cofibrantAlgebraMappingSpacePiZeroEquiv A X Y).symm _) = _
  rw [Equiv.apply_symm_apply, cofibrantAlgebraMappingSpacePiZeroEquiv_class,
    localizationHomPiZeroEquiv_arrow]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.homEquiv_map (cofibrantAlgebraWeakEquivalences A)
    ((ULiftHom.up.{u, u + 1, u + 1} (C := CofibrantAlgebra A)).map f)

/-- 概要：CAlg_R の実際の Kan Hom の π₀ は元の Map^h の π₀（Dwyer–Kan）。
方針：同じ Ex∞ 単位の π₀ 同値と元の Hom の比較を合成する。
規約：CAlg_R の Kan Hom の全単体を保持する。
使われ方：coherent nerve の写像空間比較の零次の入力。 -/
def cofibrantAlgebraKanDKPiZeroEquiv (X Y : CofibrantAlgebra A) :
    SSet.π₀ (SimplicialCategory.sHom
      (show CAlgSimplicialCategory A from cofibrantAlgebraDKObject A X)
      (show CAlgSimplicialCategory A from cofibrantAlgebraDKObject A Y)) ≃
        SSet.π₀ (((cofibrantAlgebraMappingSpace A).obj (op X)).obj Y) :=
  (kanLocalizationHomPiZeroEquiv (cofibrantAlgebraRelativeCategory A) _ _).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.homEquiv (cofibrantAlgebraWeakEquivalences A) _ _).trans
      (cofibrantAlgebraMappingSpacePiZeroEquiv A X Y).symm)

/-- 概要：Kan 化を通した元の射の類も元の Map^h の同じ類（Dwyer–Kan）。
方針：同じ単位を通した Q への正規化と元の射の式を使う。
規約：元の anodyne 単位と元の零単体の類を保持する。
使われ方：実際の CAlg_R の Kan Hom の零次の正規化。 -/
lemma cofibrantAlgebraKanDKPiZeroEquiv_class {X Y : CofibrantAlgebra A} (f : X ⟶ Y) :
    cofibrantAlgebraKanDKPiZeroEquiv A X Y
        (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app
          (localizationHom (cofibrantAlgebraRelativeCategory A)
            (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y)))
          (localizationArrowClass (cofibrantAlgebraRelativeCategory A)
            ((ULiftHom.up.{u, u + 1, u + 1} (C := CofibrantAlgebra A)).map f))) =
      mappingSpaceClass A ((cofibrantAlgebraInclusion A).map f) := by
  apply (cofibrantAlgebraMappingSpacePiZeroEquiv A X Y).injective
  change (cofibrantAlgebraMappingSpacePiZeroEquiv A X Y)
    ((cofibrantAlgebraMappingSpacePiZeroEquiv A X Y).symm _) = _
  rw [Equiv.apply_symm_apply, cofibrantAlgebraMappingSpacePiZeroEquiv_class,
    kanLocalizationHomPiZeroEquiv_arrow]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.homEquiv_map (cofibrantAlgebraWeakEquivalences A)
    ((ULiftHom.up.{u, u + 1, u + 1} (C := CofibrantAlgebra A)).map f)

end SerrePositivity.EInfinity.BarrattEccles
