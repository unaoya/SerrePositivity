module

public import SerrePositivity.InfinityCategories.HomotopyLimits.IteratedSliceOverIso

/-!
概要：反復 slice の同型が、元の図式への制限と slice の射影を対応させることを示す。
方針：展開した図式を元の右因子へ制限し、外側二因子の包含の再結合を使う。
規約：同型は元の X への射影だけでなく sliceOver p への射も保つ。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6 の native な比較 span の始点評価の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：固定図式の等式で slice の終域を移送しても族の uncurry は変わらない。
方針：図式の等式で置換して恒等射への後合成に戻す。
規約：図式の等式の証明への依存はない。
使われ方：Kerodon §4.3.6 の図式への制限の固定条件の正規化。 -/
lemma sliceOverUncurry_eqToHom {K X A : SSet.{u}} {p r : K ⟶ X}
    (h : p = r) (s : A ⟶ sliceOver p) :
    sliceOverUncurry (s ≫ eqToHom (congrArg (fun f : K ⟶ X ↦ sliceOver f) h)) =
      sliceOverUncurry s := by
  cases h
  change sliceOverUncurry (s ≫ 𝟙 (sliceOver p)) = _
  rw [Category.comp_id]

variable {K L X A : SSet.{u}} {p : K ⟶ X} (q : L ⟶ sliceOver p)

/-- 概要：展開した図式の slice を元の図式 p の slice へ制限する標準射。
方針：右因子 K への包含で制限し、展開した図式の固定条件で終域を同定する。
規約：終域は sliceOver p そのもの。
使われ方：HTT 4.2.4.1 の native な比較 span の始点評価の模型。 -/
def uncurriedSliceOverRestriction : sliceOver (sliceOverUncurry q) ⟶ sliceOver p :=
  sliceOverRestrict (sliceOverUncurry q) (joinInr L K) ≫
    eqToHom (congrArg (fun f : K ⟶ X ↦ sliceOver f) (sliceOverUncurry_fixed q))

/-- 概要：元の図式への slice の制限を展開すると右因子の包含による前合成になる。
方針：終域の図式の移送を除き、slice の制限と uncurry の可換式を使う。
規約：任意のパラメータの族について述べる。
使われ方：Kerodon 7.4.1.6 の反復 slice の射影との比較の計算。 -/
lemma uncurriedSliceOverRestriction_uncurry (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    sliceOverUncurry (s ≫ uncurriedSliceOverRestriction q) =
      joinMap (𝟙 A) (joinInr L K) ≫ sliceOverUncurry s := by
  rw [uncurriedSliceOverRestriction, ← Category.assoc,
    sliceOverUncurry_eqToHom (sliceOverUncurry_fixed q),
    sliceOverUncurry_restrict]

/-- 概要：反復 slice の族を同型で移して制限すると元の slice の射影に一致する。
方針：uncurry で検出し、外側二因子の包含と結合同型の逆の可換式を使う。
規約：全パラメータでの実際の射の厳密な等式。
使われ方：HTT 4.2.4.1 の native な比較 span の評価の追跡。 -/
lemma iteratedSliceOverForwardFamily_restriction (s : A ⟶ sliceOver q) :
    iteratedSliceOverForwardFamily q s ≫ uncurriedSliceOverRestriction q =
      s ≫ sliceOverProjection q := by
  apply sliceOverUncurry_injective p
  rw [uncurriedSliceOverRestriction_uncurry, iteratedSliceOverForwardFamily_uncurry,
    ← Category.assoc, joinAssociator_inv_outerPair, ← sliceOverUncurry_precomp,
    sliceOverUncurry_projection]

/-- 概要：反復 slice の厳密な同型は元の図式への制限と slice の射影を対応させる。
方針：恒等族における制限の公式を使う。
規約：終域は sliceOver p。単に X への射影の一致に弱めない。
使われ方：Kerodon 7.4.1.6 の比較 span の二つの中間模型の実際の評価の同定。 -/
lemma iteratedSliceOverIso_restriction :
    (iteratedSliceOverIso q).hom ≫ uncurriedSliceOverRestriction q = sliceOverProjection q := by
  simpa only [Category.id_comp, iteratedSliceOverIso, iteratedSliceOverMap] using
    iteratedSliceOverForwardFamily_restriction q (𝟙 (sliceOver q))

/-- 概要：展開した図式の slice から元の slice への制限は可変頂点の射影を保つ。
方針：反復 slice の同型の順方向で消去し、二つの射影の可換式を使う。
規約：図式・単体集合に充填性を仮定しない。
使われ方：HTT 4.2.4.1 の同じ底の頂点 fiber への比較 span の制限。 -/
lemma uncurriedSliceOverRestriction_projection :
    uncurriedSliceOverRestriction q ≫ sliceOverProjection p =
      sliceOverProjection (sliceOverUncurry q) := by
  apply (cancel_epi (iteratedSliceOverIso q).hom).1
  rw [← Category.assoc, iteratedSliceOverIso_restriction]
  exact (iteratedSliceOverIso_projection q).symm

end SerrePositivity.InfinityCategories.HomotopyLimits
