module

public import SerrePositivity.KST.Spectra.NormalizedBoundaryFilling
public import SerrePositivity.InfinityCategories.Kan.AcyclicFiber

/-!
概要：非空な Kan 複体の全ホモトピー類の消滅から、全ての単射への終対象射の RLP を導く。
方針：境界を正規化し、最後の面の類を消して充填した後、元の境界へホモトピーで戻す。
規約：全基点と零次数を含む。Kan–Quillen モデル構造の存在は使わない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2、BF 1978 §2。Whitehead の充填による証明。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：非空な Kan 複体の全ホモトピー類が一元なら任意の境界を充填できる。
方針：正次元では最後のホーンの正規化、零次元では指定頂点を使う。
規約：n は充填する標準単体の次元。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2。acyclic Kan 複体の境界 RLP。 -/
theorem exists_boundary_filler_of_homotopySubsingleton {X : SSet.{u}} [KanComplex X]
    (x₀ : X _⦋0⦌) (hπ : ∀ (x : X _⦋0⦌) (n : ℕ), Subsingleton (KanHomotopy X n x))
    (n : ℕ) (f : (boundary.{u} n : SSet.{u}) ⟶ X) :
    ∃ s : (Δ[n] : SSet.{u}) ⟶ X, (boundary n).ι ≫ s = f := by
  cases n with
  | zero => exact ⟨SSet.const x₀, boundary.hom_ext₀⟩
  | succ n =>
    obtain ⟨x, g, hg, ⟨H⟩⟩ := BoundaryNormalization.exists_normalization n f
    have hlast : KanHomotopy.mk n (BoundaryNormalization.lastSimplex n x g hg) =
        KanHomotopy.point n := (hπ x n).elim _ _
    obtain ⟨s, hs⟩ := BoundaryNormalization.exists_filler_of_lastSimplex n x g hg hlast
    exact BoundaryNormalization.exists_filler_of_homotopy (n + 1) f g H s hs

/-- 概要：上の非空な Kan 複体の終対象への射は全ての単射に RLP を持つ。
方針：境界での充填を、単射の境界 cell 分解に対する RLP の閉性へ移す。
規約：終対象射の弱同値性やモデル構造の公理を仮定しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。任意の源からの実際の収縮と持ち上げ。 -/
theorem terminal_rlp_of_homotopySubsingleton {X : SSet.{u}} [KanComplex X]
    (x₀ : X _⦋0⦌) (hπ : ∀ (x : X _⦋0⦌) (n : ℕ), Subsingleton (KanHomotopy X n x)) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from X) := by
  rw [SSet.rlp_monomorphisms]
  intro A B i hi
  rcases hi with ⟨n⟩
  constructor
  intro a b _sq
  obtain ⟨s, hs⟩ := exists_boundary_filler_of_homotopySubsingleton x₀ hπ n a
  exact CommSq.HasLift.mk' { l := s, fac_left := hs, fac_right := Subsingleton.elim _ _ }

/-- 概要：π_* 同型である Kan fibration の非空な fiber の終対象射は全単射 RLP を持つ。
方針：長完全列からの全基点の消滅を幾何的な境界充填へ戻す。
規約：fiber の頂点 v を明示する。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6。acyclic fibration の相対充填。 -/
theorem fiber_terminal_rlp_of_piIsomorphism {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (hp : KanPiIsomorphism p) (b : B _⦋0⦌)
    (v : (KanFiber p b) _⦋0⦌) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from (KanFiber p b)) :=
  terminal_rlp_of_homotopySubsingleton v (fun w n ↦ fiberHomotopySubsingleton_at p hp b w n)

end

end SerrePositivity.KST.Spectra
