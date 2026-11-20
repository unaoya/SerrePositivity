module


public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSequence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FiberComponents

/-!
概要：π_* 同型となる Kan fibration の fiber の全ホモトピー類は基点に等しい。
方針：長完全列で包含の像を消し、連結射を底の群への全射性で消す。
規約：参照頂点を全空間に明示する。境界充填への逆向きの Whitehead 補題は後続部分。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6（Tag 00WL）、BF 1978 §2。有理化用の射の実現。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : SSet.{u}} [KanComplex E] [KanComplex B]
  (p : E ⟶ B) [Fibration p]

/-- 概要：π_* 同型である Kan fibration の fiber の全次数の類は基点。
方針：包含後の類は p の単射性で消え、連結射の像は p の次次数の全射性で消える。
規約：n=0 も含む。fiber の基点は全空間の頂点 e で指定する。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6（Tag 00WL）。acyclic fiber の境界充填の入力。 -/
theorem fiberHomotopy_eq_point (hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism p) (e : E _⦋0⦌)
    (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)) n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e)) :
    a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n := by
  have hker : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n p rfl
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) a) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_fiber_total_all p e n _).2 ⟨a, rfl⟩
  have hι : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n := (hp e n).injective
    (hker.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_point n p rfl).symm)
  obtain ⟨c, hc⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_connecting_fiber_all p e n a).1 hι
  obtain ⟨d, hd⟩ := (hp e (n + 1)).surjective c
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e n c = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point n :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_total_base_all p e n c).2 ⟨d, hd⟩
  exact hc.symm.trans hz

/-- 概要：acyclic Kan fibration の fiber の指定基点のホモトピー類は一元集合。
方針：全ての類が基点に等しいことから subsingleton を構成する。
規約：零次数でも群構造を要求しない。
使われ方：Goerss–Jardine I §§7–8。fiber の消滅の集合としての表示。 -/
theorem fiberHomotopySubsingleton (hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism p) (e : E _⦋0⦌) (n : ℕ) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)) n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e)) :=
  ⟨fun a b ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberHomotopy_eq_point p hp e n a).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberHomotopy_eq_point p hp e n b).symm⟩

/-- 概要：acyclic Kan fibration の任意の fiber の任意基点で全ホモトピー類が一元。
方針：指定 fiber の頂点を全空間へ送り、その fiberPoint と同定する。
規約：空な fiber に非空性を仮定しない。基点 v を与えた場合の主張。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6（Tag 00WL）。相対充填の基点の選び直し。 -/
theorem fiberHomotopySubsingleton_at (hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism p) (b : B _⦋0⦌)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b) _⦋0⦌) (n : ℕ) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b) n v) := by
  have h : ∀ (e : E _⦋0⦌) (hb : p.app _ e = b)
      (hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b).app _ v = e),
      Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b) n v) := by
    intro e hb hv
    subst b
    have hv' : v = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e := by
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_vertex_ext p (p.app _ e)
      exact hv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e).symm
    subst v
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberHomotopySubsingleton p hp e n
  exact h ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b).app _ v) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_vertex_base p b v) rfl

/-- 概要：acyclic Kan fibration の fiber の二つの境界定数単体は相対関係で結ばれる。
方針：全次数の類の一意性を RelStruct の存在へ戻す。
規約：任意の共通境界基点と任意の面添字 i。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。正規化した境界の充填の入力。 -/
theorem fiberRelStruct_nonempty (hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism p) (b : B _⦋0⦌)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b) _⦋0⦌) (n : ℕ) (s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b).PtSimplex n v)
    (i : Fin (n + 1)) : Nonempty (PtSimplex.RelStruct s t i) := by
  let : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b) n v) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberHomotopySubsingleton_at p hp b v n
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_eq_iff_relStruct n s t i).1 (Subsingleton.elim _ _)

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
