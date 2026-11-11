module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingOuterBase
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-! # 左四角形と四頂点図式による部分長方形の分解

概要：終端角を除いた長方形は、左四角形と四頂点図式の共通 span に沿う pushout。
方針：部分複体の和と交わりを計算し、格子の双カルテジアン四角形を使う。
規約：左四角形は横座標二を含まない。使われ方：S4 の余極限頂点の付加。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：長方形の左四角形の部分複体。
方針：横座標二の頂点を除く。
規約：四頂点は横座標零または一。使われ方：五頂点図式の pushout 分解。 -/
def pastingLeftSquare : ((Δ[2] : SSet.{u}) ⊗ Δ[1]).Subcomplex where
  obj n := {s | ∀ j : Fin (n.unop.len + 1), (stdSimplex.objEquiv s.1).toOrderHom j ≠ 2}
  map α _ hs j := hs (α.unop.toOrderHom j)

/-- 概要：四頂点図式の左四角形との共通 span。
方針：四頂点図式から横座標二を除く。
規約：三頂点は (0,0)、(1,0)、(0,1)。使われ方：左四角形の押し出しの基底。 -/
def pastingLeftSpan : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase : SSet.{u}).Subcomplex where
  obj n := {s | ∀ j : Fin (n.unop.len + 1), (stdSimplex.objEquiv s.val.1).toOrderHom j ≠ 2}
  map α _ hs j := hs (α.unop.toOrderHom j)

/-- 概要：左四角形は終端角を除く部分長方形に含まれる。
方針：横座標二が存在しないことを使う。
規約：同じ長方形の部分複体の比較。使われ方：pushout の右上の包含。 -/
lemma pastingLeftSquare_le_corner : pastingLeftSquare.{u} ≤ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner := by
  intro n s hs j hx
  exact False.elim (hs j hx)

/-- 概要：左四角形と四頂点図式の和は五頂点図式である。
方針：横座標二が現れるなら最後の頂点でも二となり、縦座標が全て零になる。
規約：退化単体も含む。使われ方：格子の pushout の和の条件。 -/
lemma pastingLeftSquare_sup_outerBase :
    pastingLeftSquare.{u} ⊔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner := by
  apply le_antisymm
  · exact sup_le pastingLeftSquare_le_corner _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase_le_corner
  · intro n s hs
    change (∀ j, (stdSimplex.objEquiv s.1).toOrderHom j ≠ 2) ∨
      (∀ j, (stdSimplex.objEquiv s.2).toOrderHom j = 1 →
        (stdSimplex.objEquiv s.1).toOrderHom j = 0)
    by_cases hx : ∀ j, (stdSimplex.objEquiv s.1).toOrderHom j ≠ 2
    · exact Or.inl hx
    · right
      push Not at hx
      obtain ⟨j, hj⟩ := hx
      intro i hi
      have hjlast := (stdSimplex.objEquiv s.1).toOrderHom.monotone (Fin.le_last j)
      have hilast := (stdSimplex.objEquiv s.2).toOrderHom.monotone (Fin.le_last i)
      have hxl : (stdSimplex.objEquiv s.1).toOrderHom (Fin.last n.unop.len) = 2 := by
        exact le_antisymm (Fin.le_last _) (hj ▸ hjlast)
      have hyl : (stdSimplex.objEquiv s.2).toOrderHom (Fin.last n.unop.len) = 1 := by
        exact le_antisymm (Fin.le_last _) (hi ▸ hilast)
      exact False.elim (hs _ hxl hyl)

/-- 概要：共通 span を左四角形へ含める。
方針：二重の部分型から横座標の条件を取り出す。
規約：基底の単体を変えない。使われ方：図式の pushout の左上の射。 -/
def pastingLeftSpanToSquare : (pastingLeftSpan : SSet.{u}) ⟶ (pastingLeftSquare : SSet.{u}) where
  app _ := ↾fun s ↦ ⟨s.val.val, s.property⟩
  naturality _ _ _ := rfl

/-- 概要：共通 span と二つの部分複体の交わりは同型。
方針：二つの所属条件の入れ子と論理積を交換する。
規約：長方形の単体は変えない。使われ方：格子の pushout の移し替え。 -/
def pastingLeftSpanInfIso : (pastingLeftSpan : SSet.{u}) ≅
    ((pastingLeftSquare ⊓ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase :
      ((Δ[2] : SSet.{u}) ⊗ Δ[1]).Subcomplex) : SSet.{u}) where
  hom :=
    { app _ := ↾fun s ↦ ⟨s.val.val, s.property, s.val.property⟩
      naturality _ _ _ := rfl }
  inv :=
    { app _ := ↾fun s ↦ ⟨⟨s.val, s.property.2⟩, s.property.1⟩
      naturality _ _ _ := rfl }

/-- 概要：五頂点図式は左四角形と四頂点図式の共通 span に沿う pushout。
方針：部分複体の格子の和と交わりを使い、共通部分の表示を同型で移す。
規約：単体集合の通常の pushout。使われ方：左四角形の余極限性の付加補題への適用。 -/
lemma pastingLeftSpan_isPushout :
    IsPushout pastingLeftSpanToSquare.{u} pastingLeftSpan.ι
      (Subcomplex.homOfLE pastingLeftSquare_le_corner) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner := by
  let sq : Subcomplex.BicartSq (pastingLeftSquare ⊓ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase)
      pastingLeftSquare _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner :=
    { sup_eq := pastingLeftSquare_sup_outerBase
      inf_eq := rfl }
  apply sq.isPushout.of_iso' pastingLeftSpanInfIso (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · rfl
  · rfl
  · rfl
  · rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
