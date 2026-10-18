module

public import SerrePositivity.KST.Comparison.TensorSubcomplexEmpty
public import SerrePositivity.KST.Comparison.FiniteCoverInduction
public import SerrePositivity.KST.Comparison.SubcomplexDistributive
public import SerrePositivity.KST.Comparison.TensorSubcomplexTop

/-!
# 部分単体集合の有限被覆のホモトピー引き戻し

概要：各非空な部分族の交叉での四角形から、有限族の和での四角形を得る。
方針：空の基底、二項の和の貼り合わせ、分配束の有限帰納を合わせる。
規約：Segal 1974 Proposition 1.6 の標準単体の境界の有限被覆。
使われ方：面とその交叉の比較を境界全体へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory

/--
概要：非空な部分族の交叉で成り立つホモトピー引き戻し性は、有限族の和でも成り立つ。
方針：部分単体集合の分配束に、空・二項の和の貼り合わせの定理を適用する。
規約：面の交叉が空である場合も、空の補題で処理できる。
使われ方：fat realization の骨格の境界の各面からの比較。
-/
theorem tensorSubcomplex_homotopyPullback_finset_sup
    {X' X K T' T : SSet.{u}} {f : X' ⟶ X}
    {a : X' ⊗ K ⟶ T'} {p : T' ⟶ T} {b : X ⊗ K ⟶ T}
    (sq : CommSq a (f ▷ K) p b) {ι : Type*} (s : Finset ι) (U : ι → K.Subcomplex)
    (h : ∀ t : Finset ι, t ⊆ s → t.Nonempty →
      IsHomotopyPullback (tensorSubcomplexSquare
        (K := K) (f := f) (a := a) (p := p) (b := b) sq (t.inf U))) :
    IsHomotopyPullback (tensorSubcomplexSquare
      (K := K) (f := f) (a := a) (p := p) (b := b) sq (s.sup U)) := by
  let P : K.Subcomplex → Prop := fun V =>
    IsHomotopyPullback (tensorSubcomplexSquare (f := f) (a := a) (p := p) (b := b) sq V)
  have h0 : P ⊥ := tensorSubcomplex_homotopyPullback_bot
    (f := f) (a := a) (p := p) (b := b) sq
  have hs (V W : K.Subcomplex) (hV : P V) (hW : P W) (hI : P (V ⊓ W)) : P (V ⊔ W) :=
    tensorSubcomplex_homotopyPullback_sup (f := f) (a := a) (p := p) (b := b) sq V W hV hW hI
  have hlocal : ∀ t : Finset ι, t ⊆ s → t.Nonempty → P (t.inf U) := h
  have hout : P (s.sup U) :=
    finiteSup_of_nonempty_intersections (L := K.Subcomplex) P h0 hs s U hlocal
  exact hout

/--
概要：全体を覆う有限族の非空な交叉の比較から、元の四角形のホモトピー引き戻し性を得る。
方針：有限和の貼り合わせと、全体の部分対象への制限の保存・反映を使う。
規約：有限族の和が全体であることを明示する。
使われ方：標準単体の境界の面による有限被覆。
-/
theorem tensorSubcomplex_homotopyPullback_of_finset_cover
    {X' X K T' T : SSet.{u}} {f : X' ⟶ X}
    {a : X' ⊗ K ⟶ T'} {p : T' ⟶ T} {b : X ⊗ K ⟶ T}
    (sq : CommSq a (f ▷ K) p b) {ι : Type*} (s : Finset ι) (U : ι → K.Subcomplex)
    (hcover : s.sup U = ⊤)
    (h : ∀ t : Finset ι, t ⊆ s → t.Nonempty →
      IsHomotopyPullback (tensorSubcomplexSquare (f := f) sq (t.inf U))) :
    IsHomotopyPullback sq := by
  apply (tensorSubcomplex_homotopyPullback_top_iff sq).mp
  have hs := tensorSubcomplex_homotopyPullback_finset_sup sq s U h
  rw [hcover] at hs
  exact hs

end SerrePositivity.KST.Comparison
