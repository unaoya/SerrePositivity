module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderPresentation

/-!
# Čech–Alexander 対象の標準余積

## 概要
n 次の項を零次の n+1 個の余積として示し、site の向きで Čech データを得る。

## 方針
各頂点からの射の変数像を一つにまとめ、包絡の変数の普遍性を使う。

## 規約
BS 著者版 Construction 4.17 の最後の主張と Construction 4.18。標準頂点の脚を使う。

## 使われ方
prismatic site の Čech 脈体の古典的な構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic.CechAlexanderPresentation
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}
variable (E : ∀ n, CechAlexanderPresentation (P := P) (R := R) (κ := κ) n)

/-- 頂点ごとの射を変数像によってまとめた余積の降下射。 -/
def coproductDesc (n : ℕ) (D : PrismOver P R κ) (f : Fin (n + 1) → ((E 0).X ⟶ D)) :
    (E n).X ⟶ D :=
  ((E n).liftVariables D (fun s => (f s.2).toHom.toRingHom ((E 0).coordinate (s.1, 0)))
    (fun s => (E 0).hom_variable_mod (f s.2) (s.1, 0))).choose

/-- 余積の降下射は指定された頂点ごとの変数像を持つ。 -/
theorem coproductDesc_variable (n : ℕ) (D : PrismOver P R κ)
    (f : Fin (n + 1) → ((E 0).X ⟶ D)) (s : R × Fin (n + 1)) :
    (coproductDesc E n D f).toHom.toRingHom ((E n).coordinate s) =
      (f s.2).toHom.toRingHom ((E 0).coordinate (s.1, 0)) :=
  ((E n).liftVariables D (fun s => (f s.2).toHom.toRingHom ((E 0).coordinate (s.1, 0)))
    (fun s => (E 0).hom_variable_mod (f s.2) (s.1, 0))).choose_spec.1 s

/-- 概要：標準頂点の脚が n 次項を零次項の n+1 個の余積にする。
方針：各脚の変数像を束ねた射を作り、全ての変数で一意性を示す。
規約：BS 著者版 Construction 4.17。必要な余積のみを示す。
使われ方：Čech 余脈体と site の積の錐。 -/
def isCoproduct (n : ℕ) :
    IsColimit (Cofan.mk ((cosimplicial E).obj ⦋n⦌) (fun i : Fin (n + 1) =>
      (cosimplicial E).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i))) := by
  refine Cofan.IsColimit.mk _ (fun s => coproductDesc E n s.pt s.inj) ?_ ?_
  · intro s i
    apply (E 0).hom_ext
    intro t
    change (coproductDesc E n s.pt s.inj).toHom.toRingHom
      (((E 0).map (E n) (fun _ => i)).toHom.toRingHom ((E 0).coordinate t)) = _
    rw [map_variable, coproductDesc_variable]
    exact congrArg (fun z => (s.inj i).toHom.toRingHom ((E 0).coordinate z))
      (show (t.1, (0 : Fin 1)) = t from Prod.ext rfl (Subsingleton.elim _ _))
  · intro s g hg
    apply (E n).hom_ext
    rintro ⟨r, i⟩
    have h := congrArg (fun a : (E 0).X ⟶ s.pt =>
      a.toHom.toRingHom ((E 0).coordinate (r, 0))) (hg i)
    change g.toHom.toRingHom
      (((E 0).map (E n) (fun _ => i)).toHom.toRingHom ((E 0).coordinate (r, 0))) = _ at h
    rw [map_variable] at h
    exact h.trans (coproductDesc_variable E n s.pt s.inj (r, i)).symm

/-- 概要：環の余積の Čech–Alexander 対象を site の Čech データへ反転する。
方針：標準頂点の余積を一般の Čech データの構成へ入れる。
規約：BS 著者版 Construction 4.18。使われ方：通常の site の積のデータ。 -/
def cechNerve : CategoryTheory.CechNerveData (Opposite.op (E 0).X) :=
  CategoryTheory.CechNerveData.ofCoproducts (cosimplicial E) (isCoproduct E)

/-- 概要：site の向きでは Čech 対象の零次は弱終対象。
方針：環の向きの弱始性を反転する。
規約：BS 著者版 Construction 4.17。使われ方：Čech による計算の古典的な入力。 -/
theorem weaklyTerminal : CategoryTheory.IsWeaklyTerminal (Opposite.op (E 0).X) :=
  CategoryTheory.CechNerveData.weaklyTerminal_op ((E 0).weaklyInitial)

end SerrePositivity.BhattScholze.Prismatic.CechAlexanderPresentation

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Construction 4.17" (partial := special) "BS-W17 H3（11-11）：HasEnvelopes からの C^• の組み立て、標準余積、弱始性（site では弱終）、交代余面複体は本体。存在を供給するのは多項式の場合（D21）。C^• が Δ を計算すること（G10）は drafts ／ 11-12 夜更新（§4 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.CechAlexanderPresentation.isCoproduct
