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
open scoped BigOperators

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

private theorem projStandardProduct_degree (s : Finset ι) (hx : ∀ i, x i ∈ 𝒮 1) :
    (∏ i ∈ s, x i) ∈ 𝒮 s.card := by
  simpa using (SetLike.prod_mem_graded 𝒮 (fun _ ↦ (1 : ℕ)) x (F := s)
    (fun i _ ↦ hx i))

/--
概要：次数一の標準開の非空有限交叉上の切断を、積での次数零局所化と同一視する。
方針：積が添字集合の濃度を次数に持つことを示し、Mathlib の標準開同型を使う。
規約：交叉の開集合は積の標準開として表示する。
使われ方：構造層の Čech 複体と斉次局所化による複体の項を比較する。
-/
def projStandardIntersectionIso (s : Finset ι) (hs : s.Nonempty)
    (hx : ∀ i, x i ∈ 𝒮 1) :
    CommRingCat.of (Away 𝒮 (∏ i ∈ s, x i)) ≅
      Γ(Proj 𝒮, Proj.basicOpen 𝒮 (∏ i ∈ s, x i)) :=
  Proj.basicOpenIsoAway 𝒮 _ (projStandardProduct_degree 𝒮 x s hx) (Finset.card_pos.mpr hs)

section Restriction

variable [DecidableEq ι] {s t : Finset ι}

private theorem projStandardProduct_factor (hst : s ⊆ t) :
    (∏ i ∈ t, x i) = (∏ i ∈ s, x i) * ∏ i ∈ t \ s, x i := by
  rw [mul_comm, Finset.prod_sdiff hst]

/--
概要：添字集合を広げたときの次数零局所化の写像を与える。
方針：増えた添字の積を因子として局所化写像を作る。
規約：元の添字と新しい添字は等しくてもよい。
使われ方：標準開の Čech 複体の余面写像を作る。
-/
def projStandardIntersectionRestriction (hst : s ⊆ t) (hx : ∀ i, x i ∈ 𝒮 1) :
    CommRingCat.of (Away 𝒮 (∏ i ∈ s, x i)) ⟶ CommRingCat.of (Away 𝒮 (∏ i ∈ t, x i)) :=
  CommRingCat.ofHom (awayMap 𝒮 (projStandardProduct_degree 𝒮 x (t \ s) hx)
    (projStandardProduct_factor x hst))

/--
概要：次数零局所化の写像は標準開の切断の制限と可換になる。
方針：積に対する Mathlib の制限写像の比較を使う。
規約：元の添字集合は非空とする。
使われ方：Čech の各項の同型を余面写像に沿う同型にまとめる。
-/
theorem projStandardIntersectionIso_naturality (hs : s.Nonempty) (hst : s ⊆ t)
    (hx : ∀ i, x i ∈ 𝒮 1) :
    projStandardIntersectionRestriction 𝒮 x hst hx ≫
        (projStandardIntersectionIso 𝒮 x t (Finset.Nonempty.mono hst hs) hx).hom =
      (projStandardIntersectionIso 𝒮 x s hs hx).hom ≫ (Proj 𝒮).presheaf.map
        (homOfLE (Proj.basicOpen_mono 𝒮 _ _ ⟨_, projStandardProduct_factor x hst⟩)).op :=
  Proj.awayMap_awayToSection 𝒮 (projStandardProduct_degree 𝒮 x (t \ s) hx)
    (projStandardProduct_factor x hst)

end Restriction

end SerrePositivity.AlgebraicGeometry
