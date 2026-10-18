module

public import SerrePositivity.InfinityCategories.Core.LaxSliceUncurry

/-!
概要：太い slice の curry の後に uncurry する単位則。
方針：太い join の両因子と円柱の評価を比較する。
規約：右図式は厳密に固定する。
使われ方：Kerodon §4.6.6 の太い slice の普遍性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：curry の普遍族の左端での評価は元の太い join の左因子の値。
方針：直積の比較の左因子上の計算を使う。
規約：右図式の固定条件はこの等式には不要。
使われ方：Kerodon §4.6.6 の普遍性の単位則。 -/
lemma laxSliceLeftInput_curryFamily {A K X : SSet.{u}} (F : fatJoin A K ⟶ X) :
    laxSliceLeftInput A K ≫ laxSliceCurryFamily F = fatJoinInl A K ≫ F := by
  have hs : laxSliceLeftInput A K ≫ (β_ (fatJoin (Δ[0] : SSet.{u}) K) A).hom =
      lift (𝟙 A) (stdSimplex.isTerminalObj₀.from A) ≫ (A ◁ fatJoinInl Δ[0] K) := rfl
  rw [laxSliceCurryFamily, ← Category.assoc (laxSliceLeftInput A K), hs]
  simp only [Category.assoc]
  rw [← Category.assoc (A ◁ fatJoinInl Δ[0] K), fatJoinTensorLeft_inl]
  simp only [Category.assoc, reassoc_of% fatJoinInl_map]
  rfl

/-- 概要：curry の普遍族の円柱での評価は元の太い join の円柱の値。
方針：直積の比較の円柱上の計算と成分の並べ替えを使う。
規約：右図式の固定条件はこの等式には不要。
使われ方：Kerodon §4.6.6 の普遍性の単位則。 -/
lemma laxSliceCylinderInput_curryFamily {A K X : SSet.{u}} (F : fatJoin A K ⟶ X) :
    laxSliceCylinderInput A K ≫ laxSliceCurryFamily F = fatJoinCylinder A K ≫ F := by
  let C := (A ⊗ (Δ[1] : SSet.{u})) ⊗ K
  let c : C ⟶ A ⊗ (((Δ[0] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ⊗ K) :=
    lift (fst (A ⊗ Δ[1]) K ≫ fst A Δ[1])
      (lift (lift (stdSimplex.isTerminalObj₀.from C)
        (fst (A ⊗ Δ[1]) K ≫ snd A Δ[1])) (snd (A ⊗ Δ[1]) K))
  have hs : laxSliceCylinderInput A K ≫ (β_ (fatJoin (Δ[0] : SSet.{u}) K) A).hom =
      c ≫ (A ◁ fatJoinCylinder Δ[0] K) := rfl
  rw [laxSliceCurryFamily, ← Category.assoc (laxSliceCylinderInput A K), hs]
  simp only [Category.assoc]
  rw [← Category.assoc (A ◁ fatJoinCylinder Δ[0] K), fatJoinTensorLeft_cylinder]
  simp only [Category.assoc, reassoc_of% fatJoinCylinder_map]
  rfl

/-- 概要：太い join の関手を curry してから uncurry すると元に戻る。
方針：円柱と両因子で普遍族の評価を計算する。
規約：右図式上で p に一致することを仮定する。
使われ方：Kerodon §4.6.6 の太い slice の普遍性の一方の逆則。 -/
lemma laxSliceUncurry_curry {A K X : SSet.{u}} {p : K ⟶ X}
    (F : fatJoin A K ⟶ X) (hF : fatJoinInr A K ≫ F = p) :
    laxSliceUncurry (laxSliceCurry F hF) = F := by
  apply fatJoin_hom_ext
  · rw [laxSliceUncurry_cylinder]
    change laxSliceCylinderInput A K ≫ uncurry (curry (laxSliceCurryFamily F)) = _
    rw [uncurry_curry, laxSliceCylinderInput_curryFamily]
  · rw [laxSliceUncurry_inl]
    change laxSliceLeftInput A K ≫ uncurry (curry (laxSliceCurryFamily F)) = _
    rw [uncurry_curry, laxSliceLeftInput_curryFamily]
  · rw [laxSliceUncurry_fixed, hF]

end SerrePositivity.InfinityCategories
