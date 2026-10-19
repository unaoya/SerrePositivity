module
public import SerrePositivity.InfinityCategories.Derived.ComplexSquareComparison
public import SerrePositivity.InfinityCategories.Derived.ComplexSquarePostcomposeEdge
public import SerrePositivity.InfinityCategories.Derived.StandardSuspensionSquare

/-! # Suspension 比較の中央四角形

概要：標準 suspension の終点への後合成と、次の suspension の始点への前合成を照合する。
方針：mapping cone の包含と標準 cone 写像の合成式で二つのホモトピーを比較する。
規約：四角形の全データの等式。使われ方：D7 の実際の四角形の射の合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open CochainComplex HomComplex
open scoped Simplicial ZeroObject
variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- 標準 cofiber 四角形の鎖写像とホモトピーデータ。 -/
def cofiberComplexSquareData (f : A ⟶ B) (g : A ⟶ C) :
    ComplexSquareData A B C (pushoutCofiber f g) where
  bottom := f
  left := g
  right := pushoutInclusionB f g
  top := pushoutInclusionC f g
  diagonal := pushoutDiagonal f g
  lowerHomotopy := mappingCone.inl (cofiberDifference f g)
  upperHomotopy := 0
  lowerEquation := pushoutHomotopy_differential f g
  upperEquation := by simp only [δ_zero, pushoutDiagonal, sub_self]

/-- データから貼った四角形は既存の標準 cofiber 四角形。 -/
lemma cofiberComplexSquareData_square (f : A ⟶ B) (g : A ⟶ C) :
    (cofiberComplexSquareData f g).square = standardCofiberSquare f g := by
  apply square_isPushout.hom_ext
  · rw [ComplexSquareData.square_upper, standardCofiberSquare_upper]
    rfl
  · rw [ComplexSquareData.square_lower, standardCofiberSquare_lower]
    rfl

/-- 標準 suspension の複体四角形データ。 -/
def suspensionComplexSquareData (X : Semifree S) :
    ComplexSquareData X.val 0 0 (semifreeSuspensionObject X).val :=
  cofiberComplexSquareData 0 0

/-- 標準 cone 写像は suspension ホモトピーの包含と厳密に両立する。 -/
lemma semifreeSuspensionComplexMap_inl {X Y : Semifree S} (a : X.val ⟶ Y.val) :
    (mappingCone.inl (cofiberDifference (0 : X.val ⟶ 0) (0 : X.val ⟶ 0))).comp
        (Cochain.ofHom (semifreeSuspensionComplexMap a)) (add_zero (-1)) =
      (Cochain.ofHom a).comp
        (mappingCone.inl (cofiberDifference (0 : Y.val ⟶ 0) (0 : Y.val ⟶ 0)))
        (zero_add (-1)) := by
  unfold semifreeSuspensionComplexMap mappingCone.map
  exact mappingCone.inl_desc _ _ _ _

/-- suspension 比較を分解する二つの中央四角形は厳密に一致する。 -/
lemma suspensionComplexSquareData_middle {X Y : Semifree S} (a : X.val ⟶ Y.val) :
    ((suspensionComplexSquareData X).postcompose (semifreeSuspensionComplexMap a)) =
      (suspensionComplexSquareData Y).precompose a := by
  apply ComplexSquareData.ext
  · simp [ComplexSquareData.postcompose, ComplexSquareData.precompose,
      suspensionComplexSquareData, cofiberComplexSquareData]
  · simp [ComplexSquareData.postcompose, ComplexSquareData.precompose,
      suspensionComplexSquareData, cofiberComplexSquareData]
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _
  · simp [ComplexSquareData.postcompose, ComplexSquareData.precompose,
      suspensionComplexSquareData, cofiberComplexSquareData, pushoutDiagonal]
  · exact semifreeSuspensionComplexMap_inl a
  · simp [ComplexSquareData.postcompose, ComplexSquareData.precompose,
      suspensionComplexSquareData, cofiberComplexSquareData]

/-- 前合成と後合成を結んだ、全複体の dg nerve での suspension 四角形の射。 -/
def suspensionComplexSquareHom {X Y : Semifree S} (a : X.val ⟶ Y.val) :
    (SSet.HomotopyCategory.mk (functorVertex (suspensionComplexSquareData X).square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (dgNerve S (Complex S)))) ⟶
        SSet.HomotopyCategory.mk (functorVertex (suspensionComplexSquareData Y).square) :=
  (suspensionComplexSquareData X).comparisonHom (suspensionComplexSquareData Y)
    a (semifreeSuspensionComplexMap a) (suspensionComplexSquareData_middle a)

end SerrePositivity.InfinityCategories
