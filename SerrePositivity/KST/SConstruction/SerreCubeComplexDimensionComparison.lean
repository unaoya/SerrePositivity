module
public import SerrePositivity.KST.SConstruction.SerreCubeChainFace

/-! # 元の実鎖射の次元移送の比較
概要：元の具体的 cube 次元構造射の鎖と、同じ等号の移送を比較する。
方針：元の次元等号を消去し、元の関手の恒等保存を使う。
規約：元の実鎖射を保持。使われ方：標準一面と実 tensor 分割合成の次元移送。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の次元構造射の鎖は、同じ元の次元等号による鎖複体の移送。 -/
lemma serreCubeComplexMap_dimension_hom {p q : ℕ} (h : p = q) :
    (serreConcreteCubeComplexFunctor A).map
        (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk p) (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk q) h).hom =
      eqToHom (congrArg (serreCubeComplex A) h) := by
  cases h
  change (serreConcreteCubeComplexFunctor A).map (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk p)) = 𝟙 _
  exact (serreConcreteCubeComplexFunctor A).map_id _

/-- 元の次元構造射を前合成した実鎖射は、元の同じ実鎖射と異種等号で一致する。 -/
lemma serreCubeComplex_dimension_precomp_heq {p q : ℕ} (h : p = q) {K : Complex A}
    (f : serreCubeComplex A q ⟶ K) :
    HEq ((serreConcreteCubeComplexFunctor A).map
      (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk p) (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk q) h).hom ≫ f)
      f := by
  rw [serreCubeComplexMap_dimension_hom]
  cases h
  change HEq ((𝟙 (serreCubeComplex A p)) ≫ f) f
  exact heq_of_eq (Category.id_comp f)

end SerrePositivity.KST.SConstruction
