module

public import SerrePositivity.InfinityCategories.F2.Presentable.SourceCosliceRestrictedColimit

/-!
概要：固定始域へ制限した全余錐の頂点は、元の余錐の同じ始域への制限そのもの。
方針：反復 coslice 同型の左因子制限を計算する。
規約：頂点同型だけでなく元の構造射の厳密な等式を返す。
使われ方：指定表示段を保った compact 因子化の終点の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：制限した余錐の頂点は元の固定始域からの同じ射。
方針：反復 coslice の左制限と元の余錐値への二度の制限を計算する。
規約：元の余錐の全構造射を厳密に保つ。
使われ方：coslice 内の恒等辺の compact 因子化。 -/
lemma sourceCosliceRestrictedCocone_vertex {K A I C : SSet.{u}}
    (a : K ⟶ I) (s : A ⟶ sliceUnder a) (D : I ⟶ C) (c : JoinCocone D) :
    (sourceCosliceRestrictedCocone a s D c).vertex = c.restrict a := by
  let b := s ≫ sliceUnderPostcomp a D
  have hU : sliceUnderUncurry b = sliceUnderUncurry s ≫ D :=
    sliceUnderUncurry_postcomp s D
  let d : (sliceUnder (sliceUnderUncurry b)) _⦋0⦌ :=
    (eqToIso (congrArg sliceUnder hU.symm)).hom.app (Opposite.op ⦋0⦌)
      (c.restrict (sliceUnderUncurry s))
  have hp : (iteratedSliceUnderIso b).inv ≫ sliceUnderProjection b =
      uncurriedSliceUnderRestriction b := by
    rw [← iteratedSliceUnderIso_restriction b, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  change ((iteratedSliceUnderIso b).inv ≫ sliceUnderProjection b).app
    (Opposite.op ⦋0⦌) d = c.restrict a
  rw [hp]
  apply Subtype.ext
  change ((eqToIso (congrArg sliceUnder (sliceUnderUncurry_fixed b))).hom.app
    (Opposite.op ⦋0⦌) ((sliceUnderRestrict (sliceUnderUncurry b) (joinInl K A)).app
      (Opposite.op ⦋0⦌) d)).val = _
  rw [Ind.sliceUnder_eqToIso_val (sliceUnderUncurry_fixed b)]
  have hd : d.val = (c.restrict (sliceUnderUncurry s)).val :=
    Ind.sliceUnder_eqToIso_val hU.symm _
  change joinMap (joinInl K A) (𝟙 Δ[0]) ≫ d.val = _
  rw [hd]
  change joinMap (joinInl K A) (𝟙 Δ[0]) ≫
    (joinMap (sliceUnderUncurry s) (𝟙 Δ[0]) ≫ c.val) = _
  rw [← Category.assoc, ← joinMap_comp, Category.id_comp, sliceUnderUncurry_fixed]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable
