module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.FiberComponents

/-!
概要：固定した fiber の連結成分への連結写像の自然性。
方針：底の頂点の等式で帰納し、fiber 射の一意性と零次数の自然性を使う。
規約：全空間の参照頂点を任意に選び直せる。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6。fiber の零次数の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.FibrationSquare
end SerrePositivity.KST.Spectra.FibrationSquare
namespace SerrePositivity.InfinityCategories.Kan.FibrationSquare
open SerrePositivity.KST.Spectra.FibrationSquare

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
    (φ : KanFiber p b ⟶ KanFiber p' b') (hφ : φ ≫ fiberι p' b' = fiberι p b ≫ f)
    (a : KanHomotopyGroup B 0 (p.app _ e)) :
    mapπ₀ φ (componentConnecting p e b hb a) = componentConnecting p' (f.app _ e) b' hb'
      (KanHomotopyGroup.map g (base_eq p p' f g comm e) a) := by
  subst b
  subst b'
  have heq : φ = fiberMap p p' f g comm e := by
    apply fiber_hom_ext p' (p'.app _ (f.app _ e))
    exact hφ.trans (fiberMap_ι p p' f g comm e).symm
  subst φ
  change mapπ₀ (fiberMap p p' f g comm e) (KanHomotopyZero.equivPiZero (connecting p e 0 a)) =
    KanHomotopyZero.equivPiZero (connecting p' (f.app _ e) 0
      (KanHomotopyGroup.map g (base_eq p p' f g comm e) a))
  have h := congrArg
    (KanHomotopyZero.equivPiZero (X := KanFiber p' (p'.app _ (f.app _ e)))
      (x := fiberPoint p' (f.app _ e))) (connecting_natural p p' f g comm e 0 a)
  change KanHomotopyZero.equivPiZero
    (KanHomotopyZero.map (fiberMap p p' f g comm e) (fiberMap_point p p' f g comm e)
      (connecting p e 0 a)) = _ at h
  rw [KanHomotopyZero.equivPiZero_map] at h
  exact h

end

end SerrePositivity.InfinityCategories.Kan.FibrationSquare

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.componentConnecting_natural := _root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.componentConnecting_natural
