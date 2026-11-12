module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SelfPullbackConnectingSwap
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FiberComponentNaturality

/-!
概要：自己 pullback とその連結写像の可換四角形に関する自然性。
方針：fiber の自然性を二つの射影で自己 pullback へ移す。
規約：標的の基点は全空間の射による像とする。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop 値の逆元の射との比較。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B E' B' : SSet.{u}} (p : E ⟶ B) (p' : E' ⟶ B')
  (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')

/-- 概要：fibration の可換四角形は自己 pullback 間の射を与える。
方針：二つの射影に全空間の射を後合成する。
規約：二因子に同じ射を適用する。
使われ方：Kerodon §3.2.3（Tag 00W3）。標的の写像による二つの三角形の写像の変換。 -/
def selfPullbackMap : pullback p p ⟶ pullback p' p' :=
  pullback.lift (pullback.fst p p ≫ f) (pullback.snd p p ≫ f) (by
    rw [Category.assoc, Category.assoc, ← comm, ← Category.assoc, pullback.condition,
      Category.assoc, comm])

/-- 概要：自己 pullback の射は fiber の第一因子への包含と可換。
方針：二つの射影で fiberMap と定数射の自然性を使う。
規約：標的の参照頂点は f(e)。
使われ方：Goerss–Jardine I §7。連結射の自然性を自己 pullback へ移す。 -/
theorem selfPullbackFiberInclusion_natural (e : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap p p' f g comm =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion p' (f.app _ e) := by
  apply pullback.hom_ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion, Category.assoc,
      pullback.lift_fst, pullback.lift_fst_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_ι]
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion, Category.assoc,
      pullback.lift_snd, pullback.lift_snd_assoc, SSet.const_comp, SSet.comp_const]

/-- 概要：自己 pullback へ向かう連結写像は fibration の可換四角形に関して自然。
方針：fiber の成分の自然性に包含との可換式を合成する。
規約：底の誘導準同型の基点の等式は四角形から得る。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。交換と loop の逆元の射の比較。 -/
theorem selfPullbackConnecting_natural [Fibration p] [Fibration p']
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (e : E _⦋0⦌) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 (p.app _ e)) :
    mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap p p' f g comm) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting p e a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting p' (f.app _ e)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e) a) := by
  change mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap p p' f g comm)
    (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion p e) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting p e (p.app _ e) rfl a)) = _
  rw [← mapπ₀_comp_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion_natural p p' f g comm e,
    mapπ₀_comp_apply]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting_natural p p' f g comm e (p.app _ e) rfl
    (p'.app _ (f.app _ e)) rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_ι p p' f g comm e)]
  rfl

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackConnecting_natural := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting_natural

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackFiberInclusion_natural := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion_natural

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackMap := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackMap._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackMap.eq_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap.eq_1
