module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationNaturality

/-!
概要：標的の指定基点を持つ Kan fibration の自然性。
方針：全空間の射による基点の像と指定基点の等式で移送する。
規約：連結写像の始域・終域の基点を全て明示する。
使われ方：Goerss–Jardine I §§7–8。path fibration と loop の自然性。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.FibrationSquare
end SerrePositivity.KST.Spectra.FibrationSquare
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.FibrationSquare

variable {E B E' B' : SSet.{u}} (p : E ⟶ B) (p' : E' ⟶ B')
  (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
  (e : E _⦋0⦌) (e' : E' _⦋0⦌) (he : f.app _ e = e')

include comm he in
/-- 概要：可換正方形の底の射は指定した両基点を対応させる。
方針：通常の基点の像の式と指定基点の等式を合成する。
規約：e' は任意に指定して像との等式を与える。
使われ方：Goerss–Jardine I §7。連結写像の基点移送。 -/
theorem base_eqAt : g.app _ (p.app _ e) = p'.app _ e' :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e).trans (congrArg (p'.app _) he)

/-- 概要：指定された全空間の基点を使う fiber 間の射。
方針：基点の等式で帰納して既存の fiberMap を使う。
規約：標的は p'(e') 上の fiber。
使われ方：Goerss–Jardine I §7。定数 path の基点を保つ自然性。 -/
noncomputable def fiberMapAt : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p' (p'.app _ e') := by
  subst e'
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e

/-- 概要：指定基点の fiber 間の射は全空間への包含と可換。
方針：基点の等式で帰納する。
規約：包含後は元の全空間の射 f になる。
使われ方：Goerss–Jardine I §7。loop と fiber の同型の自然性。 -/
@[reassoc (attr := simp)]
theorem fiberMapAt_ι : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fiberMapAt p p' f g comm e e' he ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p' (p'.app _ e') =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) ≫ f := by
  subst e'
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_ι p p' f g comm e

/-- 概要：指定基点の fiber 間の射は fiberPoint を保つ。
方針：基点の等式で帰納して既存の計算を使う。
規約：標的の fiberPoint は e' によるもの。
使われ方：Goerss–Jardine I §7。ホモトピー群の誘導写像。 -/
@[simp]
theorem fiberMapAt_point :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fiberMapAt p p' f g comm e e' he).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p' e' := by
  subst e'
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_point p p' f g comm e

/-- 概要：指定基点を使う可換正方形の連結写像は全次数で自然。
方針：基点の等式で帰納して相対持ち上げによる自然性へ帰着する。
規約：零次数の fiber の類も含む。
使われ方：Goerss–Jardine I §§7–8。loop の次数移動の自然性。 -/
theorem connecting_natural_at [Fibration p] [Fibration p'] [KanComplex B] [KanComplex B']
    (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B n (p.app _ e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fiberMapAt p p' f g comm e e' he)
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fiberMapAt_point p p' f g comm e e' he) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e n a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p' e' n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.base_eqAt p p' f g comm e e' he) a) := by
  subst e'
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.connecting_natural p p' f g comm e n a

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.base_eqAt := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.base_eqAt

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.connecting_natural_at := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.connecting_natural_at

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fiberMapAt (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.fiberMapAt := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fiberMapAt

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.fiberMapAt_point := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fiberMapAt_point

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.fiberMapAt_ι := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fiberMapAt_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.fiberMapAt_ι_assoc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fiberMapAt_ι_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.fiberMapAt.congr_simp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fiberMapAt.congr_simp
