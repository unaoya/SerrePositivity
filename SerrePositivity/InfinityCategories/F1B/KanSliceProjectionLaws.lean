module

public import SerrePositivity.InfinityCategories.F1B.KanCosliceOpposite
public import SerrePositivity.InfinityCategories.Core.TerminalMap
public import SerrePositivity.InfinityCategories.Core.SliceRestriction

/-!
概要：slice の反転・後合成・制限と射影の可換性。
方針：join の両包含と Yoneda の評価を使う。
規約：同じ宇宙の小さい圏を扱う。
使われ方：B5 の左 Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet Opposite
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：coslice の反転同型は標的の反転への射影と可換。
方針：join の逆反転で左包含を元の右包含へ移す。
規約：単体集合の射の厳密な等式。
使われ方：Over の nerve の射影の照合。 -/
lemma kanSliceUnderOpIso_projection {K X : SSet.{u}} (p : K ⟶ X) :
    (kanSliceUnderOpIso p).hom ≫ sliceOverProjection (SSet.opFunctor.map p) =
      SSet.opFunctor.map (sliceUnderProjection p) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (joinInl Δ[n] K.op ≫ (kanSliceUnderOpObjEquiv p ⦋n⦌ s).val) = _
  rw [kanSliceUnderOpObjEquiv_val]
  let V : join K (Δ[n] : SSet.{u}) ⟶ X := (SSet.opObjEquiv s).val
  change SSet.yonedaEquiv (joinInl Δ[n] K.op ≫
    (joinMap (stdSimplex.opIso ⦋n⦌).inv (𝟙 K.op) ≫
      (stableJoinReverseIso K Δ[n]).inv ≫ SSet.opFunctor.map V)) =
    SSet.opObjEquiv.symm (SSet.yonedaEquiv (joinInr K Δ[n] ≫ V))
  rw [← Category.assoc, joinInl_joinMap, Category.assoc,
    reassoc_of% stableJoinReverse_inl_inv, ← SSet.opFunctor.map_comp]
  exact stableReverseSimplex_yoneda ⦋n⦌ _

/-- 概要：slice の後合成は頂点射影の後合成と可換。
方針：錐の合成の評価を計算する。
規約：任意の標的への射を扱う。
使われ方：反対 nerve の同型による標的の正規化。 -/
lemma kanSliceOverPostcomp_projection {K X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y) :
    sliceOverPostcomp p q ≫ sliceOverProjection (p ≫ q) = sliceOverProjection p ≫ q := rfl

/-- 概要：固定図式の制限は slice の頂点射影を保つ。
方針：join の左包含との可換性を使う。
規約：添字への任意の射で成立する。
使われ方：反転した零単体の正規化。 -/
lemma kanSliceOverRestrict_projection {K₀ K X : SSet.{u}} (p : K ⟶ X) (f : K₀ ⟶ K) :
    sliceOverRestrict p f ≫ sliceOverProjection (f ≫ p) = sliceOverProjection p := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (joinInl _ K₀ ≫ (joinMap (𝟙 _) f ≫ s.val)) = _
  rw [← Category.assoc, joinInl_joinMap, Category.id_comp]
  rfl


/-- 概要：図式の等式による slice の輸送は頂点射影を保つ。
方針：等式で置換し恒等同型の式へ帰着する。
規約：対象の等式でのみ輸送する。
使われ方：元の指定図式への厳密な回収。 -/
lemma kanSliceOverProjection_eqTransport {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q) :
    (eqToIso (congrArg sliceOver h)).hom ≫ sliceOverProjection q = sliceOverProjection p := by
  cases h
  simp

end SerrePositivity.InfinityCategories.F1B
