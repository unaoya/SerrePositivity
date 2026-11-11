module
public import SerrePositivity.KST.SConstruction.FirstRow
public import SerrePositivity.KST.SConstruction.FrameBoundaryExtension
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexPrescribedExtension

/-! # 第一行と零対角の枠
概要：第一行に全ての対角を追加した順序部分を扱う。
方針：第一行の順序凸性から、枠の新しい単体はどちらかの端点に対角を持つ。
規約：零対角の相対延長と cofiber 補完を分ける。
使われ方：BGT Lemma 7.3 の相対境界持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：区間が対角にある条件。
方針：両端の等号で判定する。
規約：n に依存する命題。使われ方：零対象を要求する頂点。 -/
def IsDiagonal {n : ℕ} (a : Ar.{u} n) : Prop := a.down.val.1 = a.down.val.2

/-- 概要：零対角を除いた第一行に属する条件。
方針：左端が零、右端が正であることを要求する。
規約：Fin n による第一行と一致する。使われ方：枠の既存部分。 -/
def IsPositiveRow {n : ℕ} (a : Ar.{u} n) : Prop :=
  a.down.val.1 = 0 ∧ 0 < a.down.val.2

/-- 概要：第一行は Ar[n] の順序凸部分である。
方針：上の第一行頂点から左端が零、下の第一行頂点から右端が正と分かる。
規約：対角 (0,0) は含めない。使われ方：新しい単体の端点判定。 -/
lemma positiveRow_orderConvex {n : ℕ} {a b c : Ar.{u} n}
    (ha : IsPositiveRow a) (hc : IsPositiveRow c) (hab : a ≤ b) (hbc : b ≤ c) :
    IsPositiveRow b := by
  constructor
  · apply le_antisymm
    · exact hc.1 ▸ hbc.1
    · exact Fin.zero_le _
  · exact ha.2.trans_le hab.2

/-- 概要：零を含む第一行または対角にある区間が、対角でなければ正の第一行にある。
方針：左端零の区間が対角でないことから右端が非零となる。
規約：枠の頂点の二分類。使われ方：端点の零対象性。 -/
lemma positiveRow_of_frame_not_diagonal {n : ℕ} {a : Ar.{u} n}
    (ha : a.down.val.1 = 0 ∨ IsDiagonal a) (hd : ¬ IsDiagonal a) : IsPositiveRow a := by
  refine ⟨ha.resolve_right hd, ?_⟩
  apply Fin.pos_iff_ne_zero.mpr
  intro h
  exact hd ((ha.resolve_right hd).trans h.symm)

/-- 概要：第一行・対角の枠で、第一行に含まれない鎖は端点のどちらかが対角。
方針：両端が対角でないなら正の第一行に属し、順序凸性で全鎖が第一行となる。
規約：退化鎖も扱う。使われ方：混合始点・終点境界充填の適用。 -/
lemma frameChain_diagonal_endpoint {n d : ℕ} (s : ComposableArrows (Ar.{u} n) d)
    (hs : ∀ r, (s.obj r).down.val.1 = 0 ∨ IsDiagonal (s.obj r))
    (hn : ¬ ∀ r, IsPositiveRow (s.obj r)) :
    IsDiagonal (s.obj 0) ∨ IsDiagonal (s.obj (Fin.last d)) := by
  by_contra h
  push_neg at h
  apply hn
  intro r
  exact positiveRow_orderConvex
    (positiveRow_of_frame_not_diagonal (hs 0) h.1)
    (positiveRow_of_frame_not_diagonal (hs (Fin.last d)) h.2)
    (s.monotone (Fin.zero_le r)) (s.monotone (Fin.le_last r))

/-- 概要：第一行と全対角からなる枠の順序圏。
方針：Ar[n] の順序部分型。
規約：対角間の射も保持する。使われ方：零対角を先に補う中間図式。 -/
abbrev FrameAr (n : ℕ) := {a : Ar.{u} n // a.down.val.1 = 0 ∨ IsDiagonal a}

/-- 概要：枠から Ar[n] への順序包含。
方針：部分型の値を取る。
規約：順序を反映する。使われ方：枠の鎖の端点を計算する。 -/
def frameForgetOrder (n : ℕ) : FrameAr.{u} n →o Ar.{u} n where
  toFun := Subtype.val
  monotone' _ _ h := h

/-- 概要：第一行・零対角の枠の nerve。
方針：順序圏の nerve を直接取る。
規約：全ての高次の鎖を保持する。使われ方：cofiber 補完前の図式。 -/
def frameNerve (n : ℕ) : SSet.{u} := nerve (FrameAr.{u} n)

/-- 概要：枠の中の正の第一行の全部分複体。
方針：第一行に属する頂点が張る全部分複体を取る。
規約：(0,0) は除く。使われ方：枠への制限の始域。 -/
def framePositiveRow (n : ℕ) : (frameNerve.{u} n).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (frameNerve n) (fun x ↦ IsPositiveRow (nerveEquiv x).val)

/-- 概要：第一行の外にある枠の単体はどちらかの端点が対角。
方針：順序凸性を nerve の頂点条件に書き直す。
規約：正次元の退化単体も含む。使われ方：枠の相対境界延長。 -/
lemma frameNerve_diagonal_endpoint {n d : ℕ} (s : (frameNerve.{u} n) _⦋d + 1⦌)
    (hs : s ∉ (framePositiveRow n).obj (Opposite.op ⦋d + 1⦌)) :
    IsDiagonal (nerveEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s)).val ∨
    IsDiagonal (nerveEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s)).val := by
  have hn : ¬ ∀ r, IsPositiveRow (s.obj r).val := by
    intro h
    apply hs
    intro v
    exact h (v.toOrderHom 0)
  exact frameChain_diagonal_endpoint (s ⋙ (frameForgetOrder n).toFunctor)
    (fun r ↦ (s.obj r).property) hn

/-- 概要：第一行を固定し、境界の零対角を保って枠を延長できる。
方針：新しい鎖の対角端点の零対象性を、積の混合境界延長へ渡す。
規約：正次元のパラメーター境界。安定性は不要。
使われ方：第一行制限の trivial Kan fibration の零対角段階。 -/
lemma zeroFrame_extend_boundary {X : SSet.{u}} (n d : ℕ)
    (H : frameNerve n ⊗ (boundary (d + 1) : SSet.{u}) ⟶ X)
    (G : (framePositiveRow n : SSet.{u}) ⊗ Δ[d + 1] ⟶ X)
    (hw : ((framePositiveRow n).ι ▷ (boundary (d + 1) : SSet.{u})) ≫ H =
      ((framePositiveRow n : SSet.{u}) ◁ (boundary (d + 1)).ι) ≫ G)
    (hz : ∀ (x : (frameNerve n) _⦋0⦌), IsDiagonal (nerveEquiv x).val →
      ∀ v : (boundary (d + 1) : SSet.{u}) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (H.app (Opposite.op ⦋0⦌) (x, v))) :
    ∃ F : frameNerve n ⊗ Δ[d + 1] ⟶ X,
      (frameNerve n ◁ (boundary (d + 1)).ι) ≫ F = H ∧
      ((framePositiveRow n).ι ▷ (Δ[d + 1] : SSet.{u})) ≫ F = G := by
  apply frame_extend_boundary (framePositiveRow n) d H G hw
  intro m s hs
  rcases frameNerve_diagonal_endpoint s hs with hi | ht
  · exact Or.inl (fun v ↦ (hz _ hi v).1)
  · exact Or.inr (fun v ↦ (hz _ ht v).2)

end SerrePositivity.KST.SConstruction
