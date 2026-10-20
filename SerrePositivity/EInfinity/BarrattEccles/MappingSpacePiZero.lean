module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpace
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PiZero

/-!
# E 代数の導来写像空間の π₀ と局所化後の Hom

概要：BM 命題 4.1・Hovey §5 の具体的な Map^h の π₀ は Ho(Alg_E) の Hom に一致する。
方針：frame の零次比較と fibrant 置換の比較を局所化で反転する。
規約：局所化は任意、モデル構造は具体的なものを局所的に選ぶ。
使われ方：E2a-5 の射の同定と E2b の写像空間の界面。
-/

@[expose] public section

noncomputable section

universe u v w

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

variable (A : Type u) [CommRing A]
  {H : Type w} [Category.{v} H] (L : (operad A).Algebra ⥤ H)

/-- 概要：E 代数の Map^h の π₀ と任意の局所化後の Hom の同値（Hovey §5）。
方針：具体的な分解を frame Hom の一般の π₀ 比較へ代入する。
規約：元の両代数の cofibrancy・fibrancy は入力しない。
使われ方：Ho(Alg_E) の射を実際の導来写像空間の連結成分として扱う。 -/
def mappingSpacePiZeroEquiv (X : (operad A).Algebraᵒᵖ) (Y : (operad A).Algebra) :
    let := modelCategory A
    ∀ [L.IsLocalization (weakEquivalences (operad A).Algebra)],
      SSet.π₀ (((mappingSpace A).obj X).obj Y) ≃ (L.obj X.unop ⟶ L.obj Y) := by
  let := modelCategory A
  dsimp only
  intro hL
  have := hL
  exact chosenResolutionHomPiZeroEquiv L
    (mappingCofibrantFactorization A) (mappingFibrantFactorization A) X Y

/-- 概要：π₀ と Hom の同値は元の始域の射に自然（Hovey §5）。
方針：frame の零次比較の自然性を局所化へ移す。
規約：始域の反変な向きを保持する。
使われ方：導来写像空間の前合成と Ho(Alg_E) の前合成を照合する。 -/
lemma mappingSpacePiZeroEquiv_source {X X' : (operad A).Algebraᵒᵖ} (f : X ⟶ X')
    (Y : (operad A).Algebra) (z : SSet.π₀ (((mappingSpace A).obj X).obj Y)) :
    let := modelCategory A
    ∀ [L.IsLocalization (weakEquivalences (operad A).Algebra)],
      mappingSpacePiZeroEquiv A L X' Y (SSet.mapπ₀ (((mappingSpace A).map f).app Y) z) =
        L.map f.unop ≫ mappingSpacePiZeroEquiv A L X Y z := by
  let := modelCategory A
  dsimp only
  intro hL
  have := hL
  exact chosenResolutionHomPiZeroEquiv_naturality_source L
    (mappingCofibrantFactorization A) (mappingFibrantFactorization A) f Y z

/-- 概要：π₀ と Hom の同値は元の終域の射に自然（Hovey §5）。
方針：fibrant 置換の比較の自然性を局所化へ移す。
規約：終域の共変な向きを保持する。
使われ方：導来写像空間の後合成と Ho(Alg_E) の後合成を照合する。 -/
lemma mappingSpacePiZeroEquiv_target (X : (operad A).Algebraᵒᵖ)
    {Y Y' : (operad A).Algebra} (f : Y ⟶ Y')
    (z : SSet.π₀ (((mappingSpace A).obj X).obj Y)) :
    let := modelCategory A
    ∀ [L.IsLocalization (weakEquivalences (operad A).Algebra)],
      mappingSpacePiZeroEquiv A L X Y' (SSet.mapπ₀ (((mappingSpace A).obj X).map f) z) =
        mappingSpacePiZeroEquiv A L X Y z ≫ L.map f := by
  let := modelCategory A
  dsimp only
  intro hL
  have := hL
  exact chosenResolutionHomPiZeroEquiv_naturality_target L
    (mappingCofibrantFactorization A) (mappingFibrantFactorization A) X f z

end SerrePositivity.EInfinity.BarrattEccles
