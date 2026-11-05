module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.FibrationComparison

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
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.FibrationSquare
end SerrePositivity.KST.Spectra.FibrationSquare
namespace SerrePositivity.InfinityCategories.Kan.FibrationSquare
open SerrePositivity.KST.Spectra.FibrationSquare

/-- 指定した全空間の基点とその像での正次数の全単射性から fiber を比較する。 -/
theorem fiberMap_positive_bijective_at {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (e : E _⦋0⦌)
    (hf : ∀ r, Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopy.map (r + 1) f (x := e) rfl))
    (hg : ∀ r, Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopy.map (r + 1) g (x := p.app _ e) rfl))
    (n : ℕ) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n) (_root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.fiberMap p p' f g comm e)
      (_root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.fiberMap_point p p' f g comm e)) := by
  let hb := _root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.base_eq p p' f g comm e
  have hgb (r : ℕ) : Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := r) g hb) :=
    _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopy.map_bijective_congr (r + 1) g rfl hb rfl hb (hg r)
  exact _root_.SerrePositivity.InfinityCategories.Kan.group_five_lemma
    (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n + 1) p rfl) (_root_.SerrePositivity.InfinityCategories.Kan.connectingHom p e n)
    (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n) (_root_.SerrePositivity.InfinityCategories.Kan.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kan.fiberι_point p e))
    (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n) p rfl)
    (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n + 1) p' rfl) (_root_.SerrePositivity.InfinityCategories.Kan.connectingHom p' (f.app _ e) n)
    (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n) (_root_.SerrePositivity.InfinityCategories.Kan.fiberι p' (p'.app _ (f.app _ e)))
      (_root_.SerrePositivity.InfinityCategories.Kan.fiberι_point p' (f.app _ e))) (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n) p' rfl)
    (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n + 1) f rfl) (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n + 1) g hb)
    (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n) (_root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.fiberMap p p' f g comm e) (_root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.fiberMap_point p p' f g comm e))
    (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n) f rfl) (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n) g hb)
    (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map_square p p' f g comm rfl rfl rfl hb (n + 1))
    (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.connecting_natural p p' f g comm e (n + 1) a)
    (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map_square (_root_.SerrePositivity.InfinityCategories.Kan.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kan.fiberι p' (p'.app _ (f.app _ e)))
      (_root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.fiberMap p p' f g comm e) f (_root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.fiberMap_ι p p' f g comm e).symm
        (_root_.SerrePositivity.InfinityCategories.Kan.fiberι_point p e) (_root_.SerrePositivity.InfinityCategories.Kan.fiberι_point p' (f.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.fiberMap_point p p' f g comm e) rfl n)
    (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map_square p p' f g comm rfl rfl rfl hb n)
    (_root_.SerrePositivity.InfinityCategories.Kan.exact_total_base p e n) (_root_.SerrePositivity.InfinityCategories.Kan.exact_connecting_fiber p e n) (_root_.SerrePositivity.InfinityCategories.Kan.exact_fiber_total p e n)
    (_root_.SerrePositivity.InfinityCategories.Kan.exact_total_base p' (f.app _ e) n) (_root_.SerrePositivity.InfinityCategories.Kan.exact_connecting_fiber p' (f.app _ e) n)
    (_root_.SerrePositivity.InfinityCategories.Kan.exact_fiber_total p' (f.app _ e) n)
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
    (hf : ∀ r, Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopy.map (r + 1) f (x := e) rfl))
    (hg : ∀ r, Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopy.map (r + 1) g (x := p.app _ e) rfl))
    (b : B _⦋0⦌) (hb : p.app _ e = b)
    (b' : B' _⦋0⦌) (hb' : p'.app _ (f.app _ e) = b')
    (φ : _root_.SerrePositivity.InfinityCategories.Kan.KanFiber p b ⟶ _root_.SerrePositivity.InfinityCategories.Kan.KanFiber p' b') (hφ : φ ≫ _root_.SerrePositivity.InfinityCategories.Kan.fiberι p' b' = _root_.SerrePositivity.InfinityCategories.Kan.fiberι p b ≫ f)
    (v : (_root_.SerrePositivity.InfinityCategories.Kan.KanFiber p b) _⦋0⦌) (hv : (_root_.SerrePositivity.InfinityCategories.Kan.fiberι p b).app _ v = e) (n : ℕ) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n) φ (x := v) rfl) := by
  subst b
  subst b'
  have heq : φ = _root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.fiberMap p p' f g comm e := by
    apply _root_.SerrePositivity.InfinityCategories.Kan.fiber_hom_ext p' (p'.app _ (f.app _ e))
    exact hφ.trans (_root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.fiberMap_ι p p' f g comm e).symm
  subst φ
  have hpoint : v = _root_.SerrePositivity.InfinityCategories.Kan.fiberPoint p e := by
    apply _root_.SerrePositivity.InfinityCategories.Kan.fiber_vertex_ext p (p.app _ e)
    exact hv.trans (_root_.SerrePositivity.InfinityCategories.Kan.fiberι_point p e).symm
  subst v
  exact _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopy.map_bijective_congr (n + 1) (_root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.fiberMap p p' f g comm e)
    rfl (_root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.fiberMap_point p p' f g comm e).symm (_root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.fiberMap_point p p' f g comm e) rfl
      (_root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.fiberMap_positive_bijective_at p p' f g comm e hf hg n)

end SerrePositivity.InfinityCategories.Kan.FibrationSquare

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.fiberMapOver_positive_bijective_at := _root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.fiberMapOver_positive_bijective_at

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.fiberMap_positive_bijective_at := _root_.SerrePositivity.InfinityCategories.Kan.FibrationSquare.fiberMap_positive_bijective_at
