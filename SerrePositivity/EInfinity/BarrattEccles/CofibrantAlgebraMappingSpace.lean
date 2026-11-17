module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantAlgebraLocalization
public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceClasses

/-!
# Cofibrant E 代数の同じ Kan Map^h と普通の局所化 Hom

概要：Dwyer–Kan の写像空間比較の対象となる既存の Kan Map^h を制限する。
方針：同じ包含と普通の局所化の同値で π₀ の比較を移す。
規約：写像空間を π₀ や離散単体集合へ置き換えない。厳密な合成は別に構成する。
使われ方：単体的局所化の Hom と元の Map^h の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory _root_.HomotopicalAlgebra Opposite

variable (A : Type u) [CommRing A]

/-- 概要：cofibrant E 代数上の既存の Map^h の二変数関手（Hovey §5）。
方針：元の二変数関手を同じ full subcategory の包含へ制限する。
規約：元の Kan 写像空間の全単体を保持する。
使われ方：DK 型の単体的局所化の写像空間比較。 -/
def cofibrantAlgebraMappingSpace : (CofibrantAlgebra A)ᵒᵖ ⥤ CofibrantAlgebra A ⥤ SSet.{u} :=
  (cofibrantAlgebraInclusion A).op ⋙ mappingSpace A ⋙
    (Functor.whiskeringLeft (CofibrantAlgebra A) (operad A).Algebra SSet.{u}).obj
      (cofibrantAlgebraInclusion A)

/-- 概要：制限した同じ Map^h は Kan 複体（Hovey §5）。
方針：元の写像空間の Kan 性を使う。
規約：追加のモデル構造や fibrancy 仮定は不要。
使われ方：DK 写像空間の比較先。 -/
lemma cofibrantAlgebraMappingSpace_kanComplex (X Y : CofibrantAlgebra A) :
    SSet.KanComplex (((cofibrantAlgebraMappingSpace A).obj (op X)).obj Y) :=
  mappingSpace_kanComplex A (op ((cofibrantAlgebraInclusion A).obj X))
    ((cofibrantAlgebraInclusion A).obj Y)

/-- 概要：同じ Map^h の π₀ は cofibrant 相対圏の局所化 Hom（Hovey §5）。
方針：元の Hom 比較を包含の局所化同値とその同じ因子化同型で移す。
規約：元の cofibrant 対象の局所化像をそのまま使う。
使われ方：DK 写像空間比較の零次の正規化。 -/
def cofibrantAlgebraMappingSpacePiZeroEquiv (X Y : CofibrantAlgebra A) :
    SSet.π₀ (((cofibrantAlgebraMappingSpace A).obj (op X)).obj Y) ≃
      ((cofibrantAlgebraWeakEquivalences A).Q.obj X ⟶
        (cofibrantAlgebraWeakEquivalences A).Q.obj Y) := by
  let := modelCategory A
  let Q := (weakEquivalences (operad A).Algebra).Q
  let R := (cofibrantAlgebraWeakEquivalences A).Q
  let E := cofibrantAlgebraHoEquivalence A
  let i : cofibrantAlgebraInclusion A ⋙ Q ≅ R ⋙ E.functor :=
    cofibrantAlgebraInclusionLocalizedIso A
  exact (mappingSpacePiZeroEquiv A Q (op ((cofibrantAlgebraInclusion A).obj X))
    ((cofibrantAlgebraInclusion A).obj Y)).trans
      ((Iso.homCongr (i.app X) (i.app Y)).trans E.fullyFaithfulFunctor.homEquiv.symm)

end SerrePositivity.EInfinity.BarrattEccles
