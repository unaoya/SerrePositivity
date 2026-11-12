module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingLeftSubcomplex

/-! # 左四角形の標準形

概要：左四角形の部分複体は標準の正方形 Δ[1] × Δ[1] と同型。
方針：面 δ₂ による包含と横座標の二頂点への射影を使う。
規約：縦座標を保つ。使われ方：S4 の図式の pushout と押し出し余錐の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：横座標二を一へ重ねる二頂点への単調写像。
方針：頂点番号と一の最小値を取る。
規約：左四角形上では包含の逆。使われ方：標準形の逆射。 -/
def pastingLeftProjectOrderHom : Fin 3 →o Fin 2 where
  toFun x := ⟨min x.val 1, by omega⟩
  monotone' _ _ h := min_le_min_right 1 h

/-- 概要：標準の正方形を長方形の左四角形へ写す。
方針：横座標の面 δ₂ の像を部分複体へ持ち上げる。
規約：縦座標は恒等。使われ方：左四角形の標準形。 -/
def pastingLeftSquareFromStandard : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare : SSet.{u}) :=
  Subcomplex.lift (stdSimplex.δ (2 : Fin 3) ▷ Δ[1]) (by
    intro n s hs
    obtain ⟨t, rfl⟩ := hs
    intro j
    exact (by decide : ∀ x : Fin 2, (SimplexCategory.δ (2 : Fin 3)).toOrderHom x ≠ 2)
      ((stdSimplex.objEquiv t.1).toOrderHom j))

/-- 概要：左四角形を標準の正方形へ戻す。
方針：横座標の二頂点への射影と元の縦座標を束ねる。
規約：右列には適用しない。使われ方：標準形の逆射。 -/
def pastingLeftSquareToStandard : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[1] :=
  lift (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare.ι ≫ fst Δ[2] Δ[1] ≫
    stdSimplex.map (SimplexCategory.mkHom pastingLeftProjectOrderHom))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare.ι ≫ snd Δ[2] Δ[1])

/-- 概要：標準の正方形と左四角形の部分複体の同型。
方針：横座標の二つの写像が各二頂点上で互いに逆であることを検査する。
規約：順方向は面 δ₂ の包含。使われ方：左押し出しの余錐の付加。 -/
def pastingLeftSquareIso : (Δ[1] : SSet.{u}) ⊗ Δ[1] ≅ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare : SSet.{u}) where
  hom := pastingLeftSquareFromStandard
  inv := pastingLeftSquareToStandard
  hom_inv_id := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    apply Prod.ext
    · apply stdSimplex.ext
      intro j
      exact (by decide : ∀ x : Fin 2,
        pastingLeftProjectOrderHom ((SimplexCategory.δ (2 : Fin 3)).toOrderHom x) = x) (s.1 j)
    · rfl
  inv_hom_id := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · apply stdSimplex.ext
      intro j
      exact (by decide : ∀ x : Fin 3, x ≠ 2 →
        (SimplexCategory.δ (2 : Fin 3)).toOrderHom (pastingLeftProjectOrderHom x) = x)
        (s.val.1 j) (s.property j)
    · rfl

/-- 概要：左四角形の標準形を長方形へ含めると横の面 δ₂ になる。
方針：部分複体への持ち上げを展開する。
規約：射の厳密な等式。使われ方：指定された左四角形との一致。 -/
lemma pastingLeftSquareIso_hom_ι :
    pastingLeftSquareIso.{u}.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare.ι =
      stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u}) := rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
