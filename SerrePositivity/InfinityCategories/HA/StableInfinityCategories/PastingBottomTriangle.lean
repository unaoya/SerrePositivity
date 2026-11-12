module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingLeftSquareIso

/-! # 部分長方形の底辺三角形

概要：底辺の三頂点の部分複体を標準二単体と同定し、左四角形との和と交わりを計算する。
方針：縦座標が零の条件と、横座標が二を避ける条件を用いる。
規約：長方形の横座標は Fin 3。使われ方：左四角形と合成二単体の貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：長方形の底辺の三頂点からなる部分複体。
方針：縦座標の全ての頂点が零である条件を課す。
規約：横座標には条件を課さない。使われ方：合成二単体の形状。 -/
def pastingBottomFace : ((Δ[2] : SSet.{u}) ⊗ Δ[1]).Subcomplex where
  obj _n := {s | ∀ j, (stdSimplex.objEquiv s.2).toOrderHom j = 0}
  map α _ hs j := hs (α.unop.toOrderHom j)

/-- 概要：底辺三角形は五頂点の部分長方形に含まれる。
方針：縦座標零は除かれた終端角ではない。
規約：部分複体の比較。使われ方：底辺三角形の包含。 -/
lemma pastingBottomFace_le_corner : pastingBottomFace.{u} ≤ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner := by
  intro n s hs j _ hy
  have h0 : (stdSimplex.objEquiv s.2).toOrderHom j = (0 : Fin 2) := hs j
  exact (by decide : (0 : Fin 2) ≠ 1) (h0.symm.trans hy)

/-- 概要：左四角形と底辺三角形の和は五頂点図式である。
方針：横座標二が現れたら最終頂点で縦座標零となり、全ての縦座標が零になる。
規約：任意次数の単体で計算する。使われ方：図式の pushout。 -/
lemma pastingLeftSquare_sup_bottomFace :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare.{u} ⊔ pastingBottomFace = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner := by
  apply le_antisymm
  · exact sup_le _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare_le_corner pastingBottomFace_le_corner
  · intro n s hs
    change (∀ j, (stdSimplex.objEquiv s.1).toOrderHom j ≠ 2) ∨
      (∀ j, (stdSimplex.objEquiv s.2).toOrderHom j = 0)
    by_cases hx : ∀ j, (stdSimplex.objEquiv s.1).toOrderHom j ≠ 2
    · exact Or.inl hx
    · right
      push Not at hx
      obtain ⟨j, hj⟩ := hx
      have hjlast := (stdSimplex.objEquiv s.1).toOrderHom.monotone (Fin.le_last j)
      have hxl : (stdSimplex.objEquiv s.1).toOrderHom (Fin.last n.unop.len) = 2 :=
        le_antisymm (Fin.le_last _) (hj ▸ hjlast)
      have hyl := hs _ hxl
      intro i
      have hilast := (stdSimplex.objEquiv s.2).toOrderHom.monotone (Fin.le_last i)
      have hyl0 : (stdSimplex.objEquiv s.2).toOrderHom (Fin.last n.unop.len) = (0 : Fin 2) :=
        (by decide : ∀ y : Fin 2, y ≠ 1 → y = 0) _ hyl
      exact le_antisymm (hyl0 ▸ hilast) (Fin.zero_le _)


/-- 概要：標準二単体を底辺三角形へ写す。
方針：横座標をそのまま、縦座標を零にする。
規約：自然変換を次数ごとに定義する。使われ方：底辺三角形の標準形。 -/
def pastingBottomFaceFromStandard : (Δ[2] : SSet.{u}) ⟶ (pastingBottomFace : SSet.{u}) where
  app _ := ↾fun s ↦ ⟨(s, SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) |>.app _ s),
    fun _ => rfl⟩
  naturality _ _ _ := rfl

/-- 概要：底辺三角形と標準二単体は同型である。
方針：逆写像は横座標の射影とし、縦座標が零である条件で逆則を証明する。
規約：底辺の頂点の順序は保つ。使われ方：図式の貼り合わせの標準形。 -/
def pastingBottomFaceIso : (Δ[2] : SSet.{u}) ≅ (pastingBottomFace : SSet.{u}) where
  hom := pastingBottomFaceFromStandard
  inv := pastingBottomFace.ι ≫ fst Δ[2] Δ[1]
  hom_inv_id := rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply stdSimplex.ext
      intro j
      exact (s.property j).symm

/-- 概要：左四角形と底辺三角形の共通辺は標準区間と同型である。
方針：横座標の面 δ₂ と縦座標零で写し、横座標の二頂点への射影で戻す。
規約：共通辺は (0,0)→(1,0)。使われ方：pushout の共通部分。 -/
def pastingBottomIntersectionIso : (Δ[1] : SSet.{u}) ≅
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare ⊓ pastingBottomFace :
      ((Δ[2] : SSet.{u}) ⊗ Δ[1]).Subcomplex) : SSet.{u}) where
  hom := {
    app n := ↾fun s ↦ ⟨((stdSimplex.δ (2 : Fin 3)).app n s,
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) : (Δ[1] : SSet.{u}) ⟶ Δ[1]).app n s),
      (fun j => (by decide : ∀ x : Fin 2,
        (SimplexCategory.δ (2 : Fin 3)).toOrderHom x ≠ 2) ((stdSimplex.objEquiv s).toOrderHom j)),
      fun _ => rfl⟩
    naturality _ _ _ := rfl }
  inv := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare ⊓ pastingBottomFace).ι ≫ fst Δ[2] Δ[1] ≫
    stdSimplex.map (SimplexCategory.mkHom _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftProjectOrderHom)
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply stdSimplex.ext
    intro j
    exact (by decide : ∀ x : Fin 2,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftProjectOrderHom ((SimplexCategory.δ (2 : Fin 3)).toOrderHom x) = x)
      ((stdSimplex.objEquiv s).toOrderHom j)
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · apply stdSimplex.ext
      intro j
      exact (by decide : ∀ x : Fin 3, x ≠ 2 →
        (SimplexCategory.δ (2 : Fin 3)).toOrderHom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftProjectOrderHom x) = x)
        ((stdSimplex.objEquiv s.val.1).toOrderHom j) (s.property.1 j)
    · apply stdSimplex.ext
      intro j
      exact (s.property.2 j).symm

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
