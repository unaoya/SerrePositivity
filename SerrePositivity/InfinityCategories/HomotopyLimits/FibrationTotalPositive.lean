module

public import SerrePositivity.InfinityCategories.HomotopyLimits.GroupPointedFiveLemma
public import SerrePositivity.KST.Spectra.FibrationComparison

/-!
概要：Kan fibration の比較で底と fiber の π_* 同型から全空間の全正次数の同型を得る。
方針：π₁ から fiber の π₀ へ続く箇所も含め、基点付き集合へ続く五項補題を使う。
規約：全空間の π₀ の比較は別途検証する。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2、Sp の引き戻しの Ω 条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.FibrationSquare
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：底と指定 fiber の全基点 π_* 同型は全空間の指定基点の全正次数で全単射を導く。
方針：底・fiber・全空間・底・fiber の五項列を比較し、最後の項は基点付き集合のまま扱う。
規約：n は実際の次数 n+1 を表し、n=0 も除外しない。
使われ方：Goerss–Jardine I §§7–8、引き戻しの全空間の Ω 比較の正次数部分。 -/
lemma fibrationTotal_positive_bijective {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hg : KanPiIsomorphism g) (e : E _⦋0⦌)
    (hF : KanPiIsomorphism (fiberMap p p' f g comm e)) (n : ℕ) :
    Function.Bijective (KanHomotopyGroup.map (n := n) f (x := e) rfl) := by
  let φ := fiberMap p p' f g comm e
  let hφ := fiberMap_point p p' f g comm e
  let hb := base_eq p p' f g comm e
  have hF₀ : Function.Bijective (KanHomotopy.map n φ hφ) :=
    KanHomotopy.map_bijective_congr n φ rfl hφ rfl hφ (hF (fiberPoint p e) n)
  exact group_pointed_five_lemma (KanHomotopy.point n) (KanHomotopy.point n)
    (connectingHom p e n)
    (KanHomotopyGroup.map (n := n) (fiberι p (p.app _ e)) (fiberι_point p e))
    (KanHomotopyGroup.map (n := n) p rfl) (connecting p e n)
    (connectingHom p' (f.app _ e) n)
    (KanHomotopyGroup.map (n := n) (fiberι p' (p'.app _ (f.app _ e)))
      (fiberι_point p' (f.app _ e)))
    (KanHomotopyGroup.map (n := n) p' rfl) (connecting p' (f.app _ e) n)
    (KanHomotopyGroup.map (n := n + 1) g hb)
    (KanHomotopyGroup.map (n := n) φ hφ)
    (KanHomotopyGroup.map (n := n) f rfl)
    (KanHomotopyGroup.map (n := n) g hb) (KanHomotopy.map n φ hφ)
    (fun a ↦ connecting_natural p p' f g comm e (n + 1) a)
    (KanHomotopyGroup.map_square (fiberι p (p.app _ e)) (fiberι p' (p'.app _ (f.app _ e)))
      φ f (fiberMap_ι p p' f g comm e).symm
        (fiberι_point p e) (fiberι_point p' (f.app _ e)) hφ rfl n)
    (KanHomotopyGroup.map_square p p' f g comm rfl rfl rfl hb n)
    (fun a ↦ connecting_natural p p' f g comm e n a) (KanHomotopy.map_point n φ hφ)
    (exact_connecting_fiber p e n) (exact_fiber_total p e n) (exact_total_base_all p e n)
    (exact_connecting_fiber p' (f.app _ e) n) (exact_fiber_total p' (f.app _ e) n)
    (exact_total_base_all p' (f.app _ e) n)
    (KanHomotopyGroup.map_bijective_of_piIsomorphism (n + 1) g hg hb).surjective
    (KanHomotopyGroup.map_bijective_of_piIsomorphism n φ hF hφ)
    (KanHomotopyGroup.map_bijective_of_piIsomorphism n g hg hb) hF₀.injective

end
end SerrePositivity.InfinityCategories.HomotopyLimits
