module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.StandardSuspensionSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberSquareComparisonData

/-! # Semifree の標準 cofiber 列

概要：鎖写像 f に対する span Y ← X → 0 から零角を持つ cofiber 四角形を作る。
方針：既存の Semifree cofiber 四角形と頂点計算を具体化する。
規約：三角構造は実際の押し出しから来る。使われ方：D7 の標準 cone 三角形との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial ZeroObject
variable {S : Type u} [CommRing S] {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}

/-- 鎖写像の標準 cofiber 列を与える零角付き四角形。 -/
def semifreeCofiberZeroTriangle (f : X.val ⟶ Y.val) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) where
  square := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSquare f (0 : X.val ⟶ 0)
    X.property Y.property (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_zero S)
  zero_corner := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSquare, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare_vertex01]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityZeroVertex_isZeroVertex S

/-- 標準 cofiber 列の始点は X。 -/
lemma semifreeCofiberZeroTriangle_vertex00 (f : X.val ⟶ Y.val) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (semifreeCofiberZeroTriangle f).square 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare_vertex00 _ _ _ _ _ _ _

/-- 標準 cofiber 列の右下は Y。 -/
lemma semifreeCofiberZeroTriangle_vertex10 (f : X.val ⟶ Y.val) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (semifreeCofiberZeroTriangle f).square 1 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare_vertex10 _ _ _ _ _ _ _

/-- 標準 cofiber の終点を表す Semifree 複体。 -/
def semifreeCofiberZeroObject (f : X.val ⟶ Y.val) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f (0 : X.val ⟶ 0), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_pushoutCofiber _ _
    X.property Y.property (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_zero S)⟩

/-- 標準 cofiber 列の終点は標準 cone。 -/
lemma semifreeCofiberZeroTriangle_vertex11 (f : X.val ⟶ Y.val) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (semifreeCofiberZeroTriangle f).square 1 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (semifreeCofiberZeroObject f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare_vertex11 _ _ _ _ _ _ _

/-- 標準零角付き四角形は実際の cofiber 列。 -/
lemma semifreeCofiberZeroTriangle_isCofiberSequence (f : X.val ⟶ Y.val) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence (semifreeCofiberZeroTriangle f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSquare_isPushout _ _ _ _ _

/-- 標準 cofiber 四角形の包含像は全複体の標準四角形データ。 -/
lemma semifreeCofiberZeroTriangle_inclusion (f : X.val ⟶ Y.val) :
    (semifreeCofiberZeroTriangle f).square ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData f (0 : X.val ⟶ 0)).square :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSquare_inclusion f (0 : X.val ⟶ 0)
    X.property Y.property (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_zero S)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData_square _ _).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
