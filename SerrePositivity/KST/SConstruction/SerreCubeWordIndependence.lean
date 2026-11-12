module
public import SerrePositivity.KST.SConstruction.CubeThreeNormalDetection
public import SerrePositivity.KST.SConstruction.CubeMixedPathNormalization
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordSemanticQuotient

/-! # 全生成語の Serre 評価の意味による表示非依存性
概要：同じ具体的な頂点関数を表す任意の語は、元の Serre 射でも厳密に一致する。
方針：全語の三段正規化と、中間次元を含む三段表示の単射性を合成する。
規約：形式的な関係式や選択した語の一意性は仮定しない。使われ方：具体的 □c への降下。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 同じ具体的な頂点関数を表す元の任意の語の Serre 射は一致する。 -/
lemma serreCubeWordFunctor_eq_of_vertex_eq {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords} (p q : X ⟶ Y)
    (h : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map p).val = (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map q).val) :
    (serreCubeWordFunctor A).map p = (serreCubeWordFunctor A).map q := by
  obtain ⟨r, hr, hsr⟩ := cubeWordPath_normalization A p
  obtain ⟨s, hs, hss⟩ := cubeWordPath_normalization A q
  have hrs : r = s := cubeThreeNormalVertex_injective X.dimension Y.dimension
    (hr.trans (h.trans hs.symm))
  rw [← hsr, ← hss, hrs]

/-- 元の具体的立方体の射の等号は、任意の語の Serre 評価に反映される。 -/
lemma serreCubeWordFunctor_eq_of_concrete_eq {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords} (p q : X ⟶ Y)
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map p = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map q) :
    (serreCubeWordFunctor A).map p = (serreCubeWordFunctor A).map q :=
  serreCubeWordFunctor_eq_of_vertex_eq A p q (congrArg Subtype.val h)

/-- 元の Serre 語評価を、同じ具体的関数を表す語の商へ降ろす。 -/
def serreCubeSemanticFunctor : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordSemanticQuotient ⥤ Comon (Complex A) :=
  CategoryTheory.Quotient.lift _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.homRel (serreCubeWordFunctor A)
    (fun _ _ _ _ h => serreCubeWordFunctor_eq_of_concrete_eq A _ _ h)

/-- 商上の Serre 評価は射影後に元の語評価を厳密に回収する。 -/
lemma cubeWordSemanticProjection_serre :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordSemanticProjection ⋙ serreCubeSemanticFunctor A = serreCubeWordFunctor A :=
  CategoryTheory.Quotient.lift_spec _ _ _

end SerrePositivity.KST.SConstruction
