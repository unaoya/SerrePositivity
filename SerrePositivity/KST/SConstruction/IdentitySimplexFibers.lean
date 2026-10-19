module
public import SerrePositivity.KST.SConstruction.SimplexFiberDiagram
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveStandard
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor

/-! # 恒等射の単体 fiber の可縮性
概要：恒等射の単体 fiber はパラメーター標準単体そのものであり、積の第二射影は弱同値。
方針：pullback の二射影で厳密な同型を作り、標準単体の終対象への弱同値を使う。
規約：任意の fiber の可縮性を仮定しない。使われ方：パラメーターを保持する Quillen A。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.MonoidalCategory SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 恒等射の左 fiber の標準単体からの逆射。 -/
def identitySimplexFiberSection (Y : SSet.{u}) {m : ℕ} (y : Y _⦋m⦌) :
    Δ[m] ⟶ simplexLeftFiber (𝟙 Y) y :=
  simplexLeftFiberLift (𝟙 Y) y (SSet.yonedaEquiv.symm y) (𝟙 _) (by simp)

/-- 恒等射の左 fiber は標準単体に厳密に同型。 -/
def identitySimplexFiberIso (Y : SSet.{u}) {m : ℕ} (y : Y _⦋m⦌) :
    simplexLeftFiber (𝟙 Y) y ≅ Δ[m] where
  hom := simplexLeftFiberParameter (𝟙 Y) y
  inv := identitySimplexFiberSection Y y
  hom_inv_id := by
    apply simplexLeftFiber_hom_ext (𝟙 Y) y
    · rw [Category.assoc, identitySimplexFiberSection, simplexLeftFiberLift_projection,
        Category.id_comp]
      simpa only [Category.comp_id] using (simplexLeftFiber_condition (𝟙 Y) y).symm
    · rw [Category.assoc, identitySimplexFiberSection, simplexLeftFiberLift_parameter,
        Category.comp_id, Category.id_comp]
  inv_hom_id := simplexLeftFiberLift_parameter _ _ _ _ _

/-- 恒等射の単体 fiber からテンソル単位への射は局所化同型。 -/
lemma identitySimplexFiber_toUnit_localized_isIso (Y : SSet.{u}) {m : ℕ} (y : Y _⦋m⦌) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (CartesianMonoidalCategory.toUnit (simplexLeftFiber (𝟙 Y) y))) := by
  let Q := AnodyneHomotopy.anodyneQ
  let e := stdSimplex.isTerminalObj₀.uniqueUpToIso
    (CartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{u}))
  have ht : IsIso (Q.map (stdSimplex.isTerminalObj₀.from (Δ[m] : SSet.{u}))) :=
    SimplexNerve.standardTerminal_isIso Q (Localization.inverts Q SSet.anodyneExtensions) m
  have he : CartesianMonoidalCategory.toUnit (simplexLeftFiber (𝟙 Y) y) =
      (identitySimplexFiberIso Y y).hom ≫ stdSimplex.isTerminalObj₀.from _ ≫ e.hom :=
    CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
  rw [he, Q.map_comp, Q.map_comp]
  infer_instance

/-- 恒等射の単体 fiber と Z の積の第二射影は局所化同型。 -/
lemma identitySimplexFiber_snd_localized_isIso (Y Z : SSet.{u}) {m : ℕ} (y : Y _⦋m⦌) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (CartesianMonoidalCategory.snd (simplexLeftFiber (𝟙 Y) y) Z)) := by
  have h := AnodyneHomotopy.whiskerRight_anodyneQ_isIso
    (CartesianMonoidalCategory.toUnit (simplexLeftFiber (𝟙 Y) y))
    (identitySimplexFiber_toUnit_localized_isIso Y y) Z
  rw [CartesianMonoidalCategory.snd_def, AnodyneHomotopy.anodyneQ.map_comp]
  change IsIso (AnodyneHomotopy.anodyneQ.map
    (CartesianMonoidalCategory.toUnit (simplexLeftFiber (𝟙 Y) y) ▷ Z) ≫
    AnodyneHomotopy.anodyneQ.map (λ_ Z).hom)
  infer_instance

end SerrePositivity.KST.SConstruction
