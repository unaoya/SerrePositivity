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

/-- 次数一の元の積の次数は、添字集合の濃度に等しい。 -/
theorem projStandardProduct_degree (s : Finset ι) (hx : ∀ i, x i ∈ 𝒮 1) :
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

/-- 次数一の生成元に対応する標準開は Proj のアフィン開被覆をなす。 -/
def projStandardAffineOpenCover (hx : ∀ i, x i ∈ 𝒮 1)
    (hspan : (HomogeneousIdeal.irrelevant 𝒮).toIdeal ≤ Ideal.span (Set.range x)) :
    (Proj 𝒮).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan 𝒮 x hx (fun _ ↦ Nat.zero_lt_one) hspan

/-- 次数一の標準開の非空有限交叉はアフィン開である。 -/
theorem isAffineOpen_projStandardIntersection (s : Finset ι) (hs : s.Nonempty)
    (hx : ∀ i, x i ∈ 𝒮 1) :
    IsAffineOpen (s.inf (fun i ↦ Proj.basicOpen 𝒮 (x i))) := by
  rw [← proj_basicOpen_finset_prod 𝒮 x s]
  exact Proj.isAffineOpen_basicOpen 𝒮 _ (projStandardProduct_degree 𝒮 x s hx)
    (Finset.card_pos.mpr hs)

section Restriction

variable [DecidableEq ι] {s t : Finset ι}

/-- 添字集合を広げた積を、元の積と新しい添字の積に分ける。 -/
theorem projStandardProduct_factor (hst : s ⊆ t) :
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

/-- 同じ標準開への次数零局所化の制限は恒等写像。 -/
theorem projStandardIntersectionRestriction_id (hs : s.Nonempty) (hx : ∀ i, x i ∈ 𝒮 1) :
    projStandardIntersectionRestriction 𝒮 x (show s ⊆ s from le_rfl) hx = 𝟙 _ := by
  apply (cancel_mono (projStandardIntersectionIso 𝒮 x s hs hx).hom).mp
  rw [projStandardIntersectionIso_naturality 𝒮 x hs, Category.id_comp]
  have h : (homOfLE (Proj.basicOpen_mono 𝒮 _ _
      ⟨_, projStandardProduct_factor x (show s ⊆ s from le_rfl)⟩)).op = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [h, (Proj 𝒮).presheaf.map_id, Category.comp_id]

/-- 添字集合を二度広げる制限は、一度に広げる制限と一致する。 -/
theorem projStandardIntersectionRestriction_comp {u : Finset ι}
    (hs : s.Nonempty) (hst : s ⊆ t) (htu : t ⊆ u) (hx : ∀ i, x i ∈ 𝒮 1) :
    projStandardIntersectionRestriction 𝒮 x hst hx ≫
      projStandardIntersectionRestriction 𝒮 x htu hx =
      projStandardIntersectionRestriction 𝒮 x (hst.trans htu) hx := by
  apply (cancel_mono (projStandardIntersectionIso 𝒮 x u
    (Finset.Nonempty.mono (hst.trans htu) hs) hx).hom).mp
  rw [Category.assoc,
    projStandardIntersectionIso_naturality 𝒮 x (Finset.Nonempty.mono hst hs) htu hx,
    ← Category.assoc, projStandardIntersectionIso_naturality 𝒮 x hs hst hx,
    projStandardIntersectionIso_naturality 𝒮 x hs (hst.trans htu) hx,
    Category.assoc, ← Functor.map_comp]
  congr 2

/-- 非空有限交叉の添字に対する、次数零局所化と制限写像の図式。 -/
def projStandardLocalizationDiagram (hx : ∀ i, x i ∈ 𝒮 1) :
    {s : Finset ι // s.Nonempty} ⥤ CommRingCat where
  obj s := CommRingCat.of (Away 𝒮 (∏ i ∈ s.val, x i))
  map f := projStandardIntersectionRestriction 𝒮 x (leOfHom f) hx
  map_id s := projStandardIntersectionRestriction_id 𝒮 x s.property hx
  map_comp {s _t _u} f g :=
    (projStandardIntersectionRestriction_comp 𝒮 x s.property (leOfHom f) (leOfHom g) hx).symm

/-- 非空有限交叉の添字を、Proj の開集合とその包含の逆向きの図式に送る。 -/
def projStandardOpenDiagram : {s : Finset ι // s.Nonempty} ⥤ (Proj 𝒮).Opensᵒᵖ where
  obj s := Opposite.op (Proj.basicOpen 𝒮 (∏ i ∈ s.val, x i))
  map f := (homOfLE (Proj.basicOpen_mono 𝒮 _ _ ⟨_, projStandardProduct_factor x (leOfHom f)⟩)).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/--
概要：Proj の標準開の切断の図式を、各交叉における次数零局所化の図式と比較する。
方針：各交叉の環同型を制限写像の自然性でまとめる。
規約：添字集合は非空。増大項は別途与える。
使われ方：標準開 Čech の項と余境界を同時に局所化で計算する。
-/
def projStandardLocalizationDiagramIso (hx : ∀ i, x i ∈ 𝒮 1) :
    projStandardLocalizationDiagram 𝒮 x hx ≅ projStandardOpenDiagram 𝒮 x ⋙ (Proj 𝒮).presheaf :=
  NatIso.ofComponents (fun s ↦ projStandardIntersectionIso 𝒮 x s.val s.property hx)
    (fun f ↦ projStandardIntersectionIso_naturality 𝒮 x _ (leOfHom f) hx)

end Restriction

end SerrePositivity.AlgebraicGeometry
