module

public import SerrePositivity.KST.Spectra.FibrationSequence
public import SerrePositivity.KST.Spectra.HomotopySquares
public import SerrePositivity.KST.Spectra.GroupFiveLemma

/-!
概要：Kan fibration の可換正方形で全空間と底の π_* 同型は fiber の正次数の同型を導く。
方針：自然な長完全列の五項に群の五項補題を適用する。
規約：零次数の fiber の比較はこのファイルでは主張しない。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2。fiber 列の Ω 条件の比較の準備。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.FibrationSquare

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：全空間と底が全基点 π_* 同型の可換正方形は fiber の正次数で全単射を誘導する。
方針：全空間・底・fiber・全空間・底という完全な五項列の比較を使う。
規約：次数は n+1。標的の全空間の基点は f(e)。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2。fiber の正次数の比較。 -/
theorem fiberMap_positive_bijective {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hf : KanPiIsomorphism f) (hg : KanPiIsomorphism g) (e : E _⦋0⦌) (n : ℕ) :
    Function.Bijective (KanHomotopyGroup.map (n := n) (fiberMap p p' f g comm e)
      (fiberMap_point p p' f g comm e)) := by
  let hb := base_eq p p' f g comm e
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
    (KanHomotopyGroup.map_bijective_of_piIsomorphism (n + 1) f hf rfl)
    (KanHomotopyGroup.map_bijective_of_piIsomorphism (n + 1) g hg hb)
    (KanHomotopyGroup.map_bijective_of_piIsomorphism n f hf rfl)
    (KanHomotopyGroup.map_bijective_of_piIsomorphism n g hg hb)

end

end SerrePositivity.KST.Spectra.FibrationSquare
