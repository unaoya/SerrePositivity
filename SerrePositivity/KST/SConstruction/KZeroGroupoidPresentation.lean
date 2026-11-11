module
public import SerrePositivity.KST.SConstruction.KanFundamentalPresentation
public import SerrePositivity.KST.SConstruction.KZeroFundamentalGroup

/-! # 実際の零次 K 群の Kan 置換前の基本亜群による表示
概要：実際の BF 零次 K 群を、元の境界商の辺と二単体からの基本亜群で表示する。
方針：既存の零次群と一重 S の基本群の同型に、anodyne 単位の基本群表示を合成する。
規約：元の境界商とその基点を保つ。使われ方：対象類の生成と三角圏 K₀ 比較の逆写像。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open scoped Simplicial

/-- 元の一重 S の全零境界商の、置換前の辺と二単体から作る基本亜群。 -/
abbrev boundaryFundamentalGroupoid (X : StableModel.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplicialFundamentalGroupoid (boundaryReducedRealization 0 X).right

/-- 元の境界商の基点を基本亜群の対象とする。 -/
def boundaryFundamentalBasepoint (X : StableModel.{u}) : boundaryFundamentalGroupoid X :=
  FreeGroupoid.mk (SSet.HomotopyCategory.mk (boundaryReducedRealization 0 X).basepoint)

/-- 実際の整数零次 K 群を、元の境界商の辺と二単体の基本亜群で表示する。 -/
def kZeroGroupoidPresentation (X : StableModel.{u}) :
    OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0 ≃
      (boundaryFundamentalBasepoint X ⟶ boundaryFundamentalBasepoint X) :=
  (kZeroFundamentalGroupEquiv X).toEquiv.trans
    (kanAnodyneLoopPresentation
      (B := ((boundaryKanRealizationFunctor 0).obj X).right)
      (PointedKanReplacement.unit.app (boundaryReducedRealization 0 X)).right
      (PointedKanReplacement.unit_anodyne (boundaryReducedRealization 0 X))
      (boundaryReducedRealization 0 X).basepoint)

/-- 元の零次 K 群の単位は元の基本亜群の恒等射で表示される。 -/
lemma kZeroGroupoidPresentation_one (X : StableModel.{u}) :
    kZeroGroupoidPresentation X 1 = 𝟙 _ := by
  change kanAnodyneLoopPresentation (B := ((boundaryKanRealizationFunctor 0).obj X).right)
    _ _ _ ((kZeroFundamentalGroupEquiv X) 1) = _
  rw [map_one, kanAnodyneLoopPresentation_one]
  rfl

/-- 元の零次 K 群の積は、元の辺の形式的な道の合成で表示される。 -/
lemma kZeroGroupoidPresentation_mul (X : StableModel.{u})
    (a b : OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0) :
    kZeroGroupoidPresentation X (a * b) =
      kZeroGroupoidPresentation X a ≫ kZeroGroupoidPresentation X b := by
  change kanAnodyneLoopPresentation (B := ((boundaryKanRealizationFunctor 0).obj X).right)
    _ _ _ ((kZeroFundamentalGroupEquiv X) (a * b)) = _
  rw [map_mul, kanAnodyneLoopPresentation_mul]
  rfl

/-- 元の零次 K 群の逆元は元の形式的な道の逆で表示される。 -/
lemma kZeroGroupoidPresentation_inv (X : StableModel.{u})
    (a : OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0) :
    kZeroGroupoidPresentation X a⁻¹ = inv (kZeroGroupoidPresentation X a) := by
  apply (cancel_epi (kZeroGroupoidPresentation X a)).mp
  rw [← kZeroGroupoidPresentation_mul, mul_inv_cancel, kZeroGroupoidPresentation_one,
    IsIso.hom_inv_id]

end SerrePositivity.KST.SConstruction
