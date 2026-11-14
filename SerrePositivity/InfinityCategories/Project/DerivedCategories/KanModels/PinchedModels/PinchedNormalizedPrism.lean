module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedConeInterval
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedMissingFaceZero

/-! # 正規化した差の境界上零の実 prism

概要：一段高い単体を錐写像へ引き戻し、両端が零と差、境界上零の実写像を得る。
方針：欠落頂点の後者を避ける錐写像を、零の指定面による消滅へ接続する。
規約：全ての単体次数で式を証明する。使われ方：元の二単体の相対ホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- 正規化した一段高い単体の錐 prism への引き戻し。 -/
def PinchedTopComparison.normalizedPrism {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)}
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) :
    (Δ[n + 1] : SSet.{max u v}) ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedConeIntervalMap (n + 1) ≫ SSet.yonedaEquiv.symm c.normalizedFiller.toPinched

/-- 錐 prism の零端は、零線形単体の写像。 -/
lemma PinchedTopComparison.normalizedPrism_zero {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)}
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) :
    SSet.ι₀ ≫ c.normalizedPrism =
      SSet.yonedaEquiv.symm (0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)).toPinched := by
  rw [PinchedTopComparison.normalizedPrism, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedConeIntervalMap_zero,
    SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg SSet.yonedaEquiv.symm
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedSimplex_pullback_zero_of_avoids c.normalizedFiller (0 : Fin (n + 2)).succ
  · simpa only [Fin.succ_ne_zero, ite_false] using
      c.normalizedFiller_pullback (0 : Fin (n + 2)).succ
  · intro r
    exact (Fin.succ_ne_zero (0 : Fin (n + 2))).symm

/-- 錐 prism の一端は、元の二単体の差。 -/
lemma PinchedTopComparison.normalizedPrism_one {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)}
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) :
    SSet.ι₁ ≫ c.normalizedPrism = SSet.yonedaEquiv.symm (s - t).toPinched := by
  rw [PinchedTopComparison.normalizedPrism, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedConeIntervalMap_one,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm (c.normalizedFiller_face 0)

/-- 錐 prism は元の標準単体の全境界上で零。 -/
lemma PinchedTopComparison.normalizedPrism_boundary {n : ℕ}
    {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1)} (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison s t) :
    (∂Δ[n + 1]).ι ▷ Δ[1] ≫ c.normalizedPrism =
      SSet.const (0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0).toPinched := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro p
  obtain ⟨j, hj⟩ := (SSet.mem_boundary_iff_notMem_range
    (d := d.unop.len) p.1.val).mp p.1.property
  change c.normalizedFiller.toPinched.pullback
    (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedConeIntervalOrderHom p.1.val.down.toOrderHom
      p.2.down.toOrderHom)) =
      (0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y 0).toPinched.pullback
        (SimplexCategory.const ⦋d.unop.len⦌ ⦋0⦌ 0)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedZeroSimplex_pullback]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedSimplex_pullback_zero_of_avoids c.normalizedFiller j.succ
  · simpa only [Fin.succ_ne_zero, ite_false] using c.normalizedFiller_pullback j.succ
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedConeIntervalOrderHom_avoids _ _ j (fun r h => hj ⟨r, h⟩)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
