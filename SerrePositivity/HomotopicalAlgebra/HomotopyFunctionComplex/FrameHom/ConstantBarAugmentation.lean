module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBarRows
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarPointwiseInvariance

/-!
# 定値図式の bar から元の値への augmentation

概要：定値図式の元の bar を最初のラベルへ送る射は、始対象があれば反転される。
方針：各行の射影を自然変換へ束ね、同じ対角比較を適用する。
規約：元の bar の全作用素と値の宇宙拡大を保持する。単体集合モデルは不要。
使われ方：固定右脚の値と全右脚上の bar の比較。
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar
open _root_.SerrePositivity.SimplicialModel

variable (D : Type uD) [Category.{vD} D] (K : SSet.{v})

/-- 係数次数のラベルを nerve 方向に一定に置いた二重単体集合。 -/
abbrev labels (D : Type uD) [Category.{vD} D] (K : SSet.{v}) :
    SimplexCategoryᵒᵖ ⥤ SSet.{max uD vD v} :=
  K ⋙ CategoryTheory.uliftFunctor.{max uD vD, v} ⋙ Functor.const SimplexCategoryᵒᵖ

/-- 各行の最初のラベルへの射影は全係数作用素に自然。 -/
def projectionRows :
    (BarConstruction.rows D).obj ((Functor.const D).obj K) ⟶ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.labels D K where
  app n := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.projection D (K.obj n)
  naturality _ _ _ := by ext m e; rfl

/-- 指定した基底対象への一定の射列も全係数作用素に自然。 -/
def inclusionRows (i : D) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.labels D K ⟶ (BarConstruction.rows D).obj ((Functor.const D).obj K) where
  app n := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.inclusion D (K.obj n) i
  naturality _ _ _ := by ext m x; rfl

/-- 行ごとの包含と射影の合成は元の恒等自然変換。 -/
lemma inclusionRows_projectionRows (i : D) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.inclusionRows D K i ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.projectionRows D K = 𝟙 _ := rfl

/-- ラベルの二重単体集合の対角は同じ元の単体集合の宇宙拡大。 -/
def labelsDiagonalIso : _root_.SerrePositivity.BisimplicialModel.diagonal.obj (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.labels D K) ≅
    SSet.uliftFunctor.{max uD vD, v}.obj K :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro n m θ; ext x; rfl)

/-- 元の定値図式の bar から同じ元の単体集合への射。 -/
def augmentation : (BarConstruction.functor D).obj ((Functor.const D).obj K) ⟶
    SSet.uliftFunctor.{max uD vD, v}.obj K :=
  _root_.SerrePositivity.BisimplicialModel.diagonal.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.projectionRows D K) ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.labelsDiagonalIso D K).hom

/-- 全単体で最初の元のラベルそのものを返す。 -/
lemma augmentation_app (n : SimplexCategoryᵒᵖ)
    (e : ComposableArrows (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.values D (K.obj n)).Elements n.unop.len) :
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.augmentation D K).app n e = ULift.up (e.obj 0).val := rfl

/-- 指定した対象で一定の射列を、同じ元の bar に入れる。 -/
def valueInclusion (i : D) : SSet.uliftFunctor.{max uD vD, v}.obj K ⟶
    (BarConstruction.functor D).obj ((Functor.const D).obj K) :=
  (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.labelsDiagonalIso D K).inv ≫ _root_.SerrePositivity.BisimplicialModel.diagonal.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.inclusionRows D K i)

/-- 同じ元の値への射影は値の包含の左逆。 -/
lemma valueInclusion_augmentation (i : D) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.valueInclusion D K i ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.augmentation D K = 𝟙 _ := by
  dsimp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.valueInclusion, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.augmentation]
  rw [Category.assoc, ← Category.assoc (_root_.SerrePositivity.BisimplicialModel.diagonal.map _),
    ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.inclusionRows_projectionRows,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

/-- 始対象による元の行の収縮を同じ augmentation の反転性へ移す。 -/
lemma augmentation_localized_isIso {i : D} (hi : IsInitial i) :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.augmentation D K)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.BisimplicialModel.diagonal.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.projectionRows D K))) :=
    _root_.SerrePositivity.BisimplicialModel.localized_diagonal_map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.projectionRows D K)
      (fun n => _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.projection_localized_isIso D (K.obj n) hi)
  dsimp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.augmentation]
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- 始対象があれば、任意の指定基底対象の同じ値の包含も反転される。 -/
lemma valueInclusion_localized_isIso {i : D} (hi : IsInitial i) (d : D) :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.valueInclusion D K d)) := by
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.augmentation_localized_isIso D K hi
  have h := congrArg AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.valueInclusion_augmentation D K d)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.valueInclusion D K d) ≫
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.augmentation D K)) := h.symm ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp hc

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar
