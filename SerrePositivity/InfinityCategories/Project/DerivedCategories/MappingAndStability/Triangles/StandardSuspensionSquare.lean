module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.FullCofiberVertices
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.MappingConeZeroTarget
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.StableHomotopyComparison

/-! # Semifree の標準 suspension 四角形

概要：零写像の span から実際の suspension 四角形を作り、終点を複体シフトと同定する。
方針：Semifree の標準 cofiber と四頂点の式、零終域の cone 接続同型を使う。
規約：接続同型は Mathlib の符号を保つ。使われ方：D7 の suspension 比較の具体的な模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex
open scoped _root_.Simplicial ZeroObject
variable {S : Type u} [CommRing S]

/-- Semifree 複体 X の標準 suspension 四角形。 -/
def semifreeSuspensionSquare (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) where
  square := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSquare (0 : X.val ⟶ 0) (0 : X.val ⟶ 0)
    X.property (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_zero S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_zero S)
  source_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare_vertex00 _ _ _ _ _ _ _
  zero_corner := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSquare, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare_vertex01]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityZeroVertex_isZeroVertex S
  other_zero := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSquare, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare_vertex10]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityZeroVertex_isZeroVertex S
  isPushout := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSquare_isPushout _ _ _ _ _

/-- 標準 suspension の終点を表す Semifree 複体。 -/
def semifreeSuspensionObject (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S :=
  ⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutCofiber (0 : X.val ⟶ 0) (0 : X.val ⟶ 0),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_pushoutCofiber _ _ X.property
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_zero S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_zero S)⟩

/-- 標準 suspension 四角形の終点は標準 cone の頂点。 -/
lemma semifreeSuspensionSquare_vertex (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :
    (semifreeSuspensionSquare X).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (semifreeSuspensionObject X) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare_vertex11 _ _ _ _ _ _ _

/-- 標準 suspension の複体は元の複体の一回シフトと同型。 -/
def semifreeSuspensionComplexIso (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :
    (semifreeSuspensionObject X).val ≅ X.val⟦(1 : ℤ)⟧ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mappingConeZeroTargetIso _ ((biprod_isZero_iff (0 : Complex S) 0).mpr
    ⟨isZero_zero _, isZero_zero _⟩)

/-- 鎖写像から標準 suspension の複体間の射を作る。 -/
def semifreeSuspensionComplexMap {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S} (a : X.val ⟶ Y.val) :
    (semifreeSuspensionObject X).val ⟶ (semifreeSuspensionObject Y).val :=
  mappingCone.map _ _ a (𝟙 _) (by simp [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference, biprod.lift_eq])

/-- 標準 suspension の複体シフト比較は鎖写像に対して自然。 -/
lemma semifreeSuspensionComplexIso_naturality {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S} (a : X.val ⟶ Y.val) :
    semifreeSuspensionComplexMap a ≫ (semifreeSuspensionComplexIso Y).hom =
      (semifreeSuspensionComplexIso X).hom ≫ a⟦(1 : ℤ)⟧' :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mappingConeZeroTargetIso_naturality _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
