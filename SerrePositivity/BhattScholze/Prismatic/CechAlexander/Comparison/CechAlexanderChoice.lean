module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderPresentation

/-!
# Čech–Alexander の包絡の選択の比較

## 概要
同じ変数の普遍性を持つ二族を、全ての頂点と両立する自然同型で比較する。

## 方針
恒等な頂点写像を両向きに延長し、変数の一意性から逆性と自然性を得る。

## 規約
BS 著者版 Construction 4.18。原典の定義の選択を計算模型へ比較する。

## 使われ方
HasEnvelopes で選んだ族と既存 BigCech の族の同一視。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic.CechAlexanderPresentation
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}

/-- 概要：同じ変数の普遍性を持つ二つの項の標準同型。
方針：恒等な頂点写像で両向きの射を作る。
規約：BS 著者版 Construction 4.18。使われ方：包絡の選択の比較。 -/
def termIso {n : ℕ} (E F : CechAlexanderPresentation (P := P) (R := R) (κ := κ) n) :
    E.X ≅ F.X where
  hom := E.map F id
  inv := F.map E id
  hom_inv_id := (E.map_comp F E id id).trans E.map_id
  inv_hom_id := (F.map_comp E F id id).trans F.map_id

/-- 概要：包絡の選択の比較は全ての単体射と自然に両立する。
方針：頂点写像の合成の式を二通り使う。
規約：BS 著者版 Construction 4.18。使われ方：交代余面複体へ自然な比較を誘導する。 -/
def cosimplicialIso
    (E F : ∀ n, CechAlexanderPresentation (P := P) (R := R) (κ := κ) n) :
    cosimplicial E ≅ cosimplicial F :=
  NatIso.ofComponents (fun n => termIso (E n.len) (F n.len)) (fun {m n} θ => by
    change (E m.len).map (E n.len) θ.toOrderHom ≫ (E n.len).map (F n.len) id =
      (E m.len).map (F m.len) id ≫ (F m.len).map (F n.len) θ.toOrderHom
    rw [map_comp, map_comp]
    rfl)

end SerrePositivity.BhattScholze.Prismatic.CechAlexanderPresentation
