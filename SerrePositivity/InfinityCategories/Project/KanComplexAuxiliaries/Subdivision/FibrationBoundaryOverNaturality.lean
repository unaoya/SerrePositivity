module


public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSequence

/-!
概要：参照頂点を指定し直した fiber 間の任意の射に対する連結射の自然性。
方針：頂点の等式で戻し、fiber の包含の一意性で標準の fiberMap と同定する。
規約：標的の参照頂点と基点保存の証明を明示する。
使われ方：Goerss–Jardine I §§7–8、VIII §1。点つきの塔の微分の自然性。
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

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：像と等しい指定参照頂点の fiber の射でも連結準同型は自然。
方針：参照頂点の等式と包含の一意性で元の相対ホーンの自然性に帰着する。
規約：任意の正次数の群の連結準同型を使う。
使われ方：Goerss–Jardine I §8、VIII §1。点つき fiber の比較射への適用。 -/
theorem connectingHomOver_natural {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (q : E' ⟶ B') [Fibration p] [Fibration q]
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ q)
    (e : E _⦋0⦌) (e' : E' _⦋0⦌) (he : f.app _ e = e')
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber q (q.app _ e'))
    (hφ : φ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι q (q.app _ e') = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) ≫ f)
    (hpoint : φ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint q e')
    (hb : g.app _ (p.app _ e) = q.app _ e') (r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B (r + 1) (p.app _ e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map φ hpoint (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom p e r a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom q e' r (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g hb a) := by
  subst e'
  have hφeq : φ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p q f g comm e := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext q (q.app _ (f.app _ e))
    exact hφ.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_ι p q f g comm e).symm
  subst φ
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.connecting_natural p q f g comm e (r + 1) a

end

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
