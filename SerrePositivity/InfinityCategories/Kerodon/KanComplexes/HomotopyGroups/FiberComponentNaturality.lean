module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FiberComponents

/-!
概要：固定した fiber の連結成分への連結写像の自然性。
方針：底の頂点の等式で帰納し、fiber 射の一意性と零次数の自然性を使う。
規約：全空間の参照頂点を任意に選び直せる。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6（Tag 00WL）。fiber の零次数の比較。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.FibrationSquare
end SerrePositivity.KST.Spectra.FibrationSquare
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra.FibrationSquare

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：固定した fiber の連結成分への連結写像は可換正方形に関して自然。
方針：底の頂点の移送を除き、fiber 射を普遍性で fiberMap に同定する。
規約：fiber 間の射は包含後の可換条件だけで指定できる。
使われ方：Goerss–Jardine I §§7–8。参照頂点を変えた零次数の図式。 -/
theorem componentConnecting_natural {E B E' B' : SSet.{u}} [KanComplex B] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (e : E _⦋0⦌) (b : B _⦋0⦌) (hb : p.app _ e = b)
    (b' : B' _⦋0⦌) (hb' : p'.app _ (f.app _ e) = b')
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p' b') (hφ : φ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p' b' = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b ≫ f)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 (p.app _ e)) :
    mapπ₀ φ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting p e b hb a) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting p' (f.app _ e) b' hb'
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e) a) := by
  subst b
  subst b'
  have heq : φ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p' (p'.app _ (f.app _ e))
    exact hφ.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_ι p p' f g comm e).symm
  subst φ
  change mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e 0 a)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p' (f.app _ e) 0
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e) a))
  have h := congrArg
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (X := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p' (p'.app _ (f.app _ e)))
      (x := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p' (f.app _ e))) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.connecting_natural p p' f g comm e 0 a)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_point p p' f g comm e)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e 0 a)) = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_map] at h
  exact h

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.componentConnecting_natural := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting_natural
