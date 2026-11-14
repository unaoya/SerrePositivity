module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.ComplexHomotopies.ComplexSquareComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.ComplexHomotopies.ComplexSquarePostcomposeEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.StandardSuspensionSquare

/-! # Suspension 比較の中央四角形

概要：標準 suspension の終点への後合成と、次の suspension の始点への前合成を照合する。
方針：mapping cone の包含と標準 cone 写像の合成式で二つのホモトピーを比較する。
規約：四角形の全データの等式。使われ方：D7 の実際の四角形の射の合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open CochainComplex HomComplex
open scoped _root_.Simplicial ZeroObject
variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 標準 cofiber 四角形の鎖写像とホモトピーデータ。 -/
def cofiberComplexSquareData (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData A B C (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutCofiber f g) where
  bottom := f
  left := g
  right := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB f g
  top := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionC f g
  diagonal := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutDiagonal f g
  lowerHomotopy := mappingCone.inl (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference f g)
  upperHomotopy := 0
  lowerEquation := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutHomotopy_differential f g
  upperEquation := by simp only [δ_zero, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutDiagonal, sub_self]

/-- データから貼った四角形は既存の標準 cofiber 四角形。 -/
lemma cofiberComplexSquareData_square (f : A ⟶ B) (g : A ⟶ C) :
    (cofiberComplexSquareData f g).square = _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData.square_upper, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare_upper]
    rfl
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData.square_lower, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare_lower]
    rfl

/-- 標準 suspension の複体四角形データ。 -/
def suspensionComplexSquareData (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData X.val 0 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X).val :=
  cofiberComplexSquareData 0 0

/-- 標準 cone 写像は suspension ホモトピーの包含と厳密に両立する。 -/
lemma semifreeSuspensionComplexMap_inl {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S} (a : X.val ⟶ Y.val) :
    (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference (0 : X.val ⟶ 0) (0 : X.val ⟶ 0))).comp
        (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexMap a)) (add_zero (-1)) =
      (Cochain.ofHom a).comp
        (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference (0 : Y.val ⟶ 0) (0 : Y.val ⟶ 0)))
        (zero_add (-1)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexMap mappingCone.map
  exact mappingCone.inl_desc _ _ _ _

/-- suspension 比較を分解する二つの中央四角形は厳密に一致する。 -/
lemma suspensionComplexSquareData_middle {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S} (a : X.val ⟶ Y.val) :
    ((suspensionComplexSquareData X).postcompose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexMap a)) =
      (suspensionComplexSquareData Y).precompose a := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData.ext
  · simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData.postcompose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.precompose,
      suspensionComplexSquareData, cofiberComplexSquareData]
  · simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData.postcompose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.precompose,
      suspensionComplexSquareData, cofiberComplexSquareData]
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _
  · simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData.postcompose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.precompose,
      suspensionComplexSquareData, cofiberComplexSquareData, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutDiagonal]
  · exact semifreeSuspensionComplexMap_inl a
  · simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData.postcompose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.precompose,
      suspensionComplexSquareData, cofiberComplexSquareData]

/-- 前合成と後合成を結んだ、全複体の dg nerve での suspension 四角形の射。 -/
def suspensionComplexSquareHom {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S} (a : X.val ⟶ Y.val) :
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (suspensionComplexSquareData X).square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)))) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (suspensionComplexSquareData Y).square) :=
  (suspensionComplexSquareData X).comparisonHom (suspensionComplexSquareData Y)
    a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexMap a) (suspensionComplexSquareData_middle a)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
