module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
概要：Proj の次数一標準開の有限交叉を一つの標準開にまとめる。
方針：積に対する標準開の公式と、積の斉次性を使う。
規約：交叉の添字には有限集合を使い、環の比較では非空とする。
使われ方：射影 Čech 複体の各項を斉次局所化で書く。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory HomogeneousLocalization

universe u

variable {S : Type u} [CommRing S] {σ : Type*} [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒮 : ℕ → σ) [GradedRing 𝒮]
variable {ι : Type*} (x : ι → S)

/--
概要：標準開の有限交叉を対応する元の積の標準開として表す。
方針：二元の積に対する公式を有限集合に帰納して使う。
規約：空の積は一、空の交叉は全体とする。
使われ方：Čech の添字を交叉の環に対応させる。
-/
theorem proj_basicOpen_finset_prod (s : Finset ι) :
    Proj.basicOpen 𝒮 (∏ i ∈ s, x i) = s.inf (fun i ↦ Proj.basicOpen 𝒮 (x i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Proj.basicOpen_mul, ih, Finset.inf_insert]

/--
概要：次数一の標準開の非空有限交叉上の切断を、積での次数零局所化と同一視する。
方針：積が添字集合の濃度を次数に持つことを示し、Mathlib の標準開同型を使う。
規約：同じ元の標準開が複数の添字にあってよい。
使われ方：構造層の Čech 複体と斉次局所化による複体の項を比較する。
-/
def projStandardIntersectionIso (s : Finset ι) (hs : s.Nonempty)
    (hx : ∀ i, x i ∈ 𝒮 1) :
    CommRingCat.of (Away 𝒮 (∏ i ∈ s, x i)) ≅
      Γ(Proj 𝒮, s.inf (fun i ↦ Proj.basicOpen 𝒮 (x i))) := by
  have hdeg : (∏ i ∈ s, x i) ∈ 𝒮 s.card := by
    simpa using (SetLike.prod_mem_graded 𝒮 (fun _ ↦ (1 : ℕ)) x (F := s)
      (fun i _ ↦ hx i))
  rw [← proj_basicOpen_finset_prod 𝒮 x s]
  exact Proj.basicOpenIsoAway 𝒮 _ hdeg (Finset.card_pos.mpr hs)

end SerrePositivity.AlgebraicGeometry
