module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCommonMap
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSquareHom
/-!
概要：共通宇宙の dg nerve 写像が標準単体と四角形の宇宙比較に整合する。
方針：標準単体上の写像を Yoneda で評価し、四角形の二セルを比較する。
規約：元の次数付き成分と全単体作用を保持する。
使われ方：混在宇宙の標準 cone 四角形を完全性へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} {E : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]

lemma dgNerveCommonMap_simplex (F : DGFunctor R D E) {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSimplexHomEquiv.{max u v, max u v w t} (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) n
        (SSet.yonedaEquiv.symm s) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, v, w, t} F =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSimplexHomEquiv.{max u w, max u v w t} (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) n
        (SSet.yonedaEquiv.symm (s.map F)) := by
  have hd : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSimplexHomEquiv.{max u v, max u v w t} (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) n
      (SSet.yonedaEquiv.symm s) = SSet.yonedaEquiv.symm (ULift.up s) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftYonedaMap.{max u v, max u v w t} (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) s
  have he : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSimplexHomEquiv.{max u w, max u v w t} (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) n
      (SSet.yonedaEquiv.symm (s.map F)) = SSet.yonedaEquiv.symm (ULift.up (s.map F)) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftYonedaMap.{max u w, max u v w t}
      (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) (s.map F)
  rw [hd, he, SSet.yonedaEquiv_symm_comp]
  rfl

lemma uliftSquare_triangle {X : SSet.{u}} (s : Δ[1] ⊗ Δ[1] ⟶ X) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle i ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare.{u, v} s =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSimplexHomEquiv.{u, v} X 2 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle i ≫ s) := by
  ext n x
  fin_cases i <;> rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
