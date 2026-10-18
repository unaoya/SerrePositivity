module
public import SerrePositivity.InfinityCategories.Stable.PastingCornerJoinIso
public import SerrePositivity.InfinityCategories.Stable.PastingRightSpanComparison
public import SerrePositivity.InfinityCategories.Core.PrismBaseDetection

/-! # 長方形の余錐と右四角形

概要：長方形の join 表示の右 span への制限は右四角形の余錐である。
方針：標準単体の積への射を頂点で比較し、join の二因子上で一致させる。
規約：右四角形は面 δ₀。使われ方：S4 の右四角形の押し出し判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：標準単体の積への join 上の射は二因子への制限で決まる。
方針：零単体は必ずどちらかの因子に属し、標的への射は頂点で決まることを使う。
規約：始域の二因子は任意。使われ方：余錐表示の形状の一致。 -/
lemma stableJoin_prodStdSimplex_hom_ext {K L : SSet.{u}} {m n : ℕ}
    {f g : join K L ⟶ (Δ[m] : SSet.{u}) ⊗ Δ[n]}
    (hl : joinInl K L ≫ f = joinInl K L ≫ g)
    (hr : joinInr K L ≫ f = joinInr K L ≫ g) : f = g := by
  apply prodStdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨_ | _ | k, hk⟩, a, b⟩
  · have ha : a = PUnit.unit := @Subsingleton.elim PUnit inferInstance _ _
    subst a
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hr (Opposite.op ⦋0⦌)) b
  · have hb : b = PUnit.unit := @Subsingleton.elim PUnit inferInstance _ _
    subst b
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hl (Opposite.op ⦋0⦌)) a
  · change k + 2 < 2 at hk
    omega

/-- 概要：長方形の余錐を右 span に制限すると右四角形の余錐表示に一致する。
方針：基底上では右 span の包含の式、余錐頂点上では正方形の第一三角形を使う。
規約：値域を選ぶ前の形状の厳密な等式。
使われ方：部分長方形の余極限性と右四角形の押し出し性の同定。 -/
lemma pastingCornerCocone_rightSpan :
    joinMap (pastingRightSpanIso.{u}.hom ≫ pastingRightSpan.ι) (𝟙 Δ[0]) ≫
      pastingCornerCocone =
    spanCoconeSquareIso.hom ≫ (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) := by
  apply stableJoin_prodStdSimplex_hom_ext
  · rw [← Category.assoc, joinInl_joinMap, Category.assoc, pastingCornerCocone_inl]
    exact pastingRightSpanIso_hom_ι
  · rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
    have hv : joinInr (horn 2 0 : SSet.{u}) Δ[0] =
        joinInr Δ[1] Δ[0] ≫ (joinStdSimplexIso 1 0).hom ≫ spanCoconeTriangleLeft := by
      simp only [spanCoconeTriangleLeft, Iso.hom_inv_id_assoc]
      rw [joinInr_joinMap, Category.id_comp]
    rw [hv]
    simp only [Category.assoc, reassoc_of% spanCoconeSquareIso_left]
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide

/-- 概要：同じ射で表される余錐は余極限性が一致する。
方針：基底の等式も余錐の固定条件から復元し、部分型の等式に帰着する。
規約：基底の図式は定義的に同じでなくてもよい。
使われ方：形状の等式による余極限性の移し替え。 -/
lemma isColimitCone_iff_of_val_eq {K X : SSet.{u}} {p q : K ⟶ X}
    (c : JoinCocone p) (d : JoinCocone q) (h : c.val = d.val) :
    IsColimitCone c ↔ IsColimitCone d := by
  have hp : p = q := by rw [← c.property, ← d.property, h]
  subst q
  have hd : c = d := Subtype.ext h
  subst d
  rfl

/-- 概要：長方形を終端角への余錐とみなす。
方針：join 表示で前合成し、左因子上の等式を使う。
規約：基底は終端角を除く五頂点図式。
使われ方：S4 の貼り合わせの普遍性。 -/
def pastingCocone {X : SSet.{u}} (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    JoinCocone (pastingCorner.ι ≫ F) :=
  ⟨pastingCornerCocone ≫ F, by rw [← Category.assoc, pastingCornerCocone_inl]⟩

/-- 概要：長方形の五頂点図式上の余極限性は右四角形の押し出し性と同値。
方針：右 span への制限で余極限性を判定し、制限した余錐の形状を右四角形と同定する。
規約：値域に quasicategory 性のみを仮定する。
使われ方：S4 の貼り合わせの右側の普遍性。 -/
lemma pastingCocone_isColimitCone_iff_right {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    IsColimitCone (pastingCocone F) ↔ IsPushoutSquare (pastingSquare F 0) := by
  refine (pastingCorner_isColimitCone_iff_standardSpan (pastingCocone F)).trans ?_
  apply isColimitCone_iff_of_val_eq
  dsimp only [JoinCocone.restrict, pastingCocone, pushoutCocone, pastingSquare]
  rw [← Category.assoc, pastingCornerCocone_rightSpan, Category.assoc]

end SerrePositivity.InfinityCategories
