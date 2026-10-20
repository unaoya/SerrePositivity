module

public import SerrePositivity.KST.Spectra.FibrationComparison

/-!
概要：fiber の正次数の比較には、指定基点での全空間と底の同型性だけで十分。
方針：同じ長完全列の五項補題を、実際に使う四つの基点での全単射性に適用する。
規約：他の連結成分の基点の同型性は要求しない。使われ方：loop 値の全基点検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.FibrationSquare

/-- 指定した全空間の基点とその像での正次数の全単射性から fiber を比較する。 -/
theorem fiberMap_positive_bijective_at {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (e : E _⦋0⦌)
    (hf : ∀ r, Function.Bijective (KanHomotopy.map (r + 1) f (x := e) rfl))
    (hg : ∀ r, Function.Bijective (KanHomotopy.map (r + 1) g (x := p.app _ e) rfl))
    (n : ℕ) :
    Function.Bijective (KanHomotopyGroup.map (n := n) (fiberMap p p' f g comm e)
      (fiberMap_point p p' f g comm e)) := by
  let hb := base_eq p p' f g comm e
  have hgb (r : ℕ) : Function.Bijective (KanHomotopyGroup.map (n := r) g hb) :=
    KanHomotopy.map_bijective_congr (r + 1) g rfl hb rfl hb (hg r)
  exact group_five_lemma
    (KanHomotopyGroup.map (n := n + 1) p rfl) (connectingHom p e n)
    (KanHomotopyGroup.map (n := n) (fiberι p (p.app _ e)) (fiberι_point p e))
    (KanHomotopyGroup.map (n := n) p rfl)
    (KanHomotopyGroup.map (n := n + 1) p' rfl) (connectingHom p' (f.app _ e) n)
    (KanHomotopyGroup.map (n := n) (fiberι p' (p'.app _ (f.app _ e)))
      (fiberι_point p' (f.app _ e))) (KanHomotopyGroup.map (n := n) p' rfl)
    (KanHomotopyGroup.map (n := n + 1) f rfl) (KanHomotopyGroup.map (n := n + 1) g hb)
    (KanHomotopyGroup.map (n := n) (fiberMap p p' f g comm e) (fiberMap_point p p' f g comm e))
    (KanHomotopyGroup.map (n := n) f rfl) (KanHomotopyGroup.map (n := n) g hb)
    (KanHomotopyGroup.map_square p p' f g comm rfl rfl rfl hb (n + 1))
    (fun a ↦ connecting_natural p p' f g comm e (n + 1) a)
    (KanHomotopyGroup.map_square (fiberι p (p.app _ e)) (fiberι p' (p'.app _ (f.app _ e)))
      (fiberMap p p' f g comm e) f (fiberMap_ι p p' f g comm e).symm
        (fiberι_point p e) (fiberι_point p' (f.app _ e)) (fiberMap_point p p' f g comm e) rfl n)
    (KanHomotopyGroup.map_square p p' f g comm rfl rfl rfl hb n)
    (exact_total_base p e n) (exact_connecting_fiber p e n) (exact_fiber_total p e n)
    (exact_total_base p' (f.app _ e) n) (exact_connecting_fiber p' (f.app _ e) n)
    (exact_fiber_total p' (f.app _ e) n)
    (hf (n + 1))
    (hgb (n + 1))
    (hf n)
    (hgb n)


/-- 固定した fiber の任意の頂点で、指定全空間・底の基点の正次数だけを使う。 -/
theorem fiberMapOver_positive_bijective_at {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (e : E _⦋0⦌)
    (hf : ∀ r, Function.Bijective (KanHomotopy.map (r + 1) f (x := e) rfl))
    (hg : ∀ r, Function.Bijective (KanHomotopy.map (r + 1) g (x := p.app _ e) rfl))
    (b : B _⦋0⦌) (hb : p.app _ e = b)
    (b' : B' _⦋0⦌) (hb' : p'.app _ (f.app _ e) = b')
    (φ : KanFiber p b ⟶ KanFiber p' b') (hφ : φ ≫ fiberι p' b' = fiberι p b ≫ f)
    (v : (KanFiber p b) _⦋0⦌) (hv : (fiberι p b).app _ v = e) (n : ℕ) :
    Function.Bijective (KanHomotopyGroup.map (n := n) φ (x := v) rfl) := by
  subst b
  subst b'
  have heq : φ = fiberMap p p' f g comm e := by
    apply fiber_hom_ext p' (p'.app _ (f.app _ e))
    exact hφ.trans (fiberMap_ι p p' f g comm e).symm
  subst φ
  have hpoint : v = fiberPoint p e := by
    apply fiber_vertex_ext p (p.app _ e)
    exact hv.trans (fiberι_point p e).symm
  subst v
  exact KanHomotopy.map_bijective_congr (n + 1) (fiberMap p p' f g comm e)
    rfl (fiberMap_point p p' f g comm e).symm (fiberMap_point p p' f g comm e) rfl
      (fiberMap_positive_bijective_at p p' f g comm e hf hg n)

end SerrePositivity.KST.Spectra.FibrationSquare
