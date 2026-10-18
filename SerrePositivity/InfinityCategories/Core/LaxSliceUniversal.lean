module

public import SerrePositivity.InfinityCategories.Core.LaxSliceCurryUnit

/-!
概要：太い slice の任意のパラメーターに対する普遍性。
方針：太い join の円柱と両因子で curry と uncurry の二つの逆則を示す。
規約：右図式は高次単体でも厳密に固定する。
使われ方：Kerodon §4.6.4・4.6.6 の太い slice の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：太い slice の射を uncurry した族は元の関手単体集合の族に戻る。
方針：円柱と左右の因子上で計算し、零単体の一意性を使う。
規約：quasicategory 性は不要。
使われ方：Kerodon §4.6.6 の普遍性の第二の逆則。 -/
lemma laxSliceCurryFamily_uncurry {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ laxSlice p) :
    laxSliceCurryFamily (laxSliceUncurry f) = uncurry (f ≫ vertexFiberι _ (functorVertex p)) := by
  apply fatJoin_tensorRight_hom_ext
  · have hs : (fatJoinCylinder (Δ[0] : SSet.{u}) K ▷ A) ≫
        (β_ (fatJoin (Δ[0] : SSet.{u}) K) A).hom =
      (β_ (((Δ[0] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ⊗ K) A).hom ≫
        (A ◁ fatJoinCylinder Δ[0] K) := rfl
    rw [laxSliceCurryFamily, ← Category.assoc (fatJoinCylinder (Δ[0] : SSet.{u}) K ▷ A), hs]
    simp only [Category.assoc]
    rw [← Category.assoc (A ◁ fatJoinCylinder Δ[0] K), fatJoinTensorLeft_cylinder]
    simp only [Category.assoc, reassoc_of% fatJoinCylinder_map,
      reassoc_of% laxSliceUncurry_cylinder]
    rw [laxSliceUncurry_cylinder]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨⟨z, t⟩, k⟩, a⟩
    have hz : (stdSimplex.isTerminalObj₀.from A).app (Opposite.op ⦋n⦌) a = z := by
      apply stdSimplex.ext
      intro i
      omega
    change (uncurry (f ≫ vertexFiberι _ (functorVertex p))).app (Opposite.op ⦋n⦌)
      ((fatJoinCylinder Δ[0] K).app (Opposite.op ⦋n⦌)
        (((stdSimplex.isTerminalObj₀.from A).app (Opposite.op ⦋n⦌) a, t), k), a) = _
    rw [hz]
    rfl
  · have hs : (fatJoinInl (Δ[0] : SSet.{u}) K ▷ A) ≫
        (β_ (fatJoin (Δ[0] : SSet.{u}) K) A).hom =
      (β_ (Δ[0] : SSet.{u}) A).hom ≫ (A ◁ fatJoinInl Δ[0] K) := rfl
    rw [laxSliceCurryFamily, ← Category.assoc (fatJoinInl (Δ[0] : SSet.{u}) K ▷ A), hs]
    simp only [Category.assoc]
    rw [← Category.assoc (A ◁ fatJoinInl Δ[0] K), fatJoinTensorLeft_inl]
    simp only [Category.assoc, reassoc_of% fatJoinInl_map, reassoc_of% laxSliceUncurry_inl]
    rw [laxSliceUncurry_inl]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨z, a⟩
    have hz : (stdSimplex.isTerminalObj₀.from A).app (Opposite.op ⦋n⦌) a = z := by
      apply stdSimplex.ext
      intro i
      omega
    change (uncurry (f ≫ vertexFiberι _ (functorVertex p))).app (Opposite.op ⦋n⦌)
      ((fatJoinInl Δ[0] K).app (Opposite.op ⦋n⦌)
        ((stdSimplex.isTerminalObj₀.from A).app (Opposite.op ⦋n⦌) a), a) = _
    rw [hz]
    rfl
  · rw [laxSliceCurryFamily_fixed _ (laxSliceUncurry_fixed f), laxSliceFamily_fixed]

/-- 概要：太い slice への射を uncurry して curry すると元に戻る。
方針：fiber の包含後に uncurry した普遍族を比較する。
規約：quasicategory 性は不要。
使われ方：Kerodon §4.6.6 の太い slice の普遍性の逆則。 -/
lemma laxSliceCurry_uncurry {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ laxSlice p) :
    laxSliceCurry (laxSliceUncurry f) (laxSliceUncurry_fixed f) = f := by
  apply vertexFiber_hom_ext ((pre (fatJoinInr (Δ[0] : SSet.{u}) K)).app X) (functorVertex p)
  change curry (laxSliceCurryFamily (laxSliceUncurry f)) = f ≫ vertexFiberι _ (functorVertex p)
  apply uncurry_injective
  rw [uncurry_curry, laxSliceCurryFamily_uncurry]

/-- 概要：太い slice への射と右図式を固定する太い join 上の射は同値。
方針：curry と uncurry の二つの逆則を使う。
規約：A、K、X の quasicategory 性・非空性は不要。
使われ方：Kerodon §4.6.4・4.6.6 の太い slice の普遍性。 -/
noncomputable def laxSliceHomEquiv {K X : SSet.{u}} (p : K ⟶ X) (A : SSet.{u}) :
    (A ⟶ laxSlice p) ≃ {F : fatJoin A K ⟶ X // fatJoinInr A K ≫ F = p} where
  toFun f := ⟨laxSliceUncurry f, laxSliceUncurry_fixed f⟩
  invFun F := laxSliceCurry F.val F.property
  left_inv := laxSliceCurry_uncurry
  right_inv F := Subtype.ext (laxSliceUncurry_curry F.val F.property)

end SerrePositivity.InfinityCategories
