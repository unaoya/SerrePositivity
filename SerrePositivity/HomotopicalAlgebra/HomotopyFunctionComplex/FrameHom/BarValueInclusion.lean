module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBarAugmentation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarInitialComparison

/-!
# 全遷移が反転される図式の各値から bar への包含

概要：始対象を持つ添字圏では、全遷移が反転される図式の各値の包含も反転される。
方針：始対象の値の定値図式からの比較と、その定値 bar の値の包含を合成する。
規約：元の各値の零でない次数も全て同じ一定の基底射列へ送る。
使われ方：元の固定右脚の Hom から全右脚の bar への射の反転。
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows
open _root_.SerrePositivity.SimplicialModel

variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})

/-- 元の値の単体を、同じ基底対象とラベルの一定の射列に送る。 -/
def valueInclusion (d : D) : SSet.uliftFunctor.{max uD vD, v}.obj (F.obj d) ⟶
    (BarConstruction.functor D).obj F where
  app n := ↾fun x => (Functor.const _).obj ((F.flip.obj n).elementsMk d x.down)
  naturality _ _ _ := rfl

/-- 定値図式からの元の比較に対する、各値の包含の厳密な自然性。 -/
lemma constantInclusion_naturality (K : SSet.{v})
    (η : (Functor.const D).obj K ⟶ F) (d : D) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.valueInclusion D K d ≫ (BarConstruction.functor D).map η =
      SSet.uliftFunctor.{max uD vD, v}.map (η.app d) ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.valueInclusion F d := by
  ext n x
  rfl

/-- 始対象と全遷移の不変性から、任意の固定値の元の包含が反転される。 -/
lemma valueInclusion_localized_isIso {i : D} (hi : IsInitial i)
    (hF : ∀ {d e : D} (f : d ⟶ e),
      IsIso (AnodyneHomotopy.anodyneQ.map (F.map f))) (d : D) :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.valueInclusion F d)) := by
  let η := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.fromInitial F hi
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.valueInclusion D (F.obj i) d)) :=
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.valueInclusion_localized_isIso D (F.obj i) hi d
  have : IsIso (AnodyneHomotopy.anodyneQ.map ((BarConstruction.functor D).map η)) :=
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.fromInitial_localized_isIso F hi hF
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (SSet.uliftFunctor.{max uD vD, v}.map (η.app d))) :=
    UniverseLift.anodyneQ_map_isIso_of_small _ (hF (hi.to d))
  have h := congrArg AnodyneHomotopy.anodyneQ.map
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.constantInclusion_naturality F (F.obj i) η d)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map
      (SSet.uliftFunctor.{max uD vD, v}.map (η.app d)) ≫
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.valueInclusion F d)) := h ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hc

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows
