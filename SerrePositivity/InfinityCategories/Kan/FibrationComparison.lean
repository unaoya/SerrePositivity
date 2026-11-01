module

public import SerrePositivity.InfinityCategories.Kan.FibrationComparisonPositive
public import SerrePositivity.InfinityCategories.Kan.FibrationComparisonZero

/-!
概要：Kan fibration の可換正方形で全空間と底の π_* 同型は fiber の全基点 π_* 同型を導く。
方針：正次数の五項補題と、参照頂点を選び直す零次数の証明を合成する。
規約：固定した fiber の任意の頂点を基点として扱う。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6、BF 1978 §2。fiber 列の Ω 条件。
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

/-- 概要：包含と可換な固定 fiber の射は指定頂点で正次数の全単射を誘導する。
方針：底の等式で移送し、参照頂点を fiberPoint に同定して五項補題を使う。
規約：φ は全空間への包含後で指定される任意の fiber の射。
使われ方：Goerss–Jardine I §§7–8。fiber の任意基点での正次数比較。 -/
theorem fiberMapOver_positive_bijective {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hf : KanPiIsomorphism f) (hg : KanPiIsomorphism g)
    (e : E _⦋0⦌) (b : B _⦋0⦌) (hb : p.app _ e = b)
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
      (fiberMap_positive_bijective p p' f g comm hf hg e n)

/-- 概要：全空間と底が全基点 π_* 同型の可換正方形は fiber の全基点 π_* 同型を導く。
方針：零次数は連結成分の比較、正次数は fiber の任意頂点を参照基点として五項補題を使う。
規約：零次数を含む全自然数次数を実際の L9 の誘導写像で検証する。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2。スペクトルの fiber の Ω 条件の比較。 -/
theorem fiberMap_piIsomorphism {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hf : KanPiIsomorphism f) (hg : KanPiIsomorphism g) (e₀ : E _⦋0⦌) :
    KanPiIsomorphism (fiberMap p p' f g comm e₀) := by
  intro v n
  cases n with
  | zero =>
    exact (KanHomotopyZero.map_bijective_iff_piZero (fiberMap p p' f g comm e₀)
      (x := v) rfl).2 (fiberMap_piZero_bijective p p' f g comm hf hg e₀)
  | succ n =>
    let e := (fiberι p (p.app _ e₀)).app _ v
    have hb : p.app _ e = p.app _ e₀ := fiber_vertex_base p (p.app _ e₀) v
    have hb' : p'.app _ (f.app _ e) = p'.app _ (f.app _ e₀) :=
      (base_eq p p' f g comm e).symm.trans
        ((congrArg (g.app _) hb).trans (base_eq p p' f g comm e₀))
    exact fiberMapOver_positive_bijective p p' f g comm hf hg e (p.app _ e₀) hb
      (p'.app _ (f.app _ e₀)) hb' (fiberMap p p' f g comm e₀)
        (fiberMap_ι p p' f g comm e₀) v rfl n

/-- 概要：包含と可換な固定 fiber の射は全基点 π_* 同型。
方針：底の指定頂点の等式で移送し、fiber の普遍性で標準の fiberMap と同定する。
規約：源の参照頂点 e の存在を明示する。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2。loop の fiber 表示を使う Ω 条件。 -/
theorem fiberMapOver_piIsomorphism {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hf : KanPiIsomorphism f) (hg : KanPiIsomorphism g)
    (e : E _⦋0⦌) (b : B _⦋0⦌) (hb : p.app _ e = b)
    (b' : B' _⦋0⦌) (hb' : p'.app _ (f.app _ e) = b')
    (φ : KanFiber p b ⟶ KanFiber p' b') (hφ : φ ≫ fiberι p' b' = fiberι p b ≫ f) :
    KanPiIsomorphism φ := by
  subst b
  subst b'
  have heq : φ = fiberMap p p' f g comm e := by
    apply fiber_hom_ext p' (p'.app _ (f.app _ e))
    exact hφ.trans (fiberMap_ι p p' f g comm e).symm
  subst φ
  exact fiberMap_piIsomorphism p p' f g comm hf hg e

end

end SerrePositivity.KST.Spectra.FibrationSquare
