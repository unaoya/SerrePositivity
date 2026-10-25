module

public import SerrePositivity.InfinityCategories.F2.Presentable.PiAdjunctionUnit

/-!
概要：元の小さい族の全随伴を全直積の全随伴へまとめる。
方針：構成した全単位の全 Hom 比較を成分ごとの全単射として検証する。
規約：全余単位と両三角式を構成し、随伴関手定理は使わない。
使われ方：小さい積の反映模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：小さい族の元の随伴関手の全直積は全随伴をなす。
方針：元の単位 Hom 比較を各成分の全単射の全直積へ分解する。
規約：元の各随伴の単位を使う。
使われ方：小さい全直積の反映像の生成対象の構成。 -/
def piAdjunction {ι : Type u} {C D : ι → SSet.{u + 1}}
    [∀ i, Quasicategory (C i)] [∀ i, Quasicategory (D i)]
    {F : ∀ i, C i ⟶ D i} {R : ∀ i, D i ⟶ C i}
    (a : ∀ i, QCatAdjunction (F i) (R i)) : QCatAdjunction (piSSetMap F) (piSSetMap R) := by
  apply qcatAdjunctionOfUnitHomBijective (piAdjunctionUnit a)
  intro A hA U V
  let p := functorHomPiEquiv (U ≫ piSSetMap F) V
  let q := functorHomPiEquiv U (V ≫ piSSetMap R)
  let m := Equiv.piCongrRight (fun i ↦ (a i).homEquiv
    (U ≫ piSSetProjection C i) (V ≫ piSSetProjection D i))
  let e : FunctorHom (U ≫ piSSetMap F) V ≃ FunctorHom U (V ≫ piSSetMap R) :=
    p.trans (m.trans q.symm)
  have he : qcatUnitHomMap (piAdjunctionUnit a) U V = e := by
    funext α
    apply q.injective
    have h := q.apply_symm_apply (m (p α))
    have hc : q (qcatUnitHomMap (piAdjunctionUnit a) U V α) = m (p α) := by
      funext i
      exact piAdjunctionUnit_homMap_components a U V α i
    exact hc.trans h.symm
  rw [he]
  exact e.bijective

end SerrePositivity.InfinityCategories.F2.Presentable
