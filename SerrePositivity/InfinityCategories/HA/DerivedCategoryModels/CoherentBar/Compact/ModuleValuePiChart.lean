module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeHomSmallPiChart
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PiChartSpaceCast
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UnderlyingValueRestriction
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentHomSection
/-!
概要：実加群の native 基礎空間を、元の評価複体の全基点コホモロジーへ同定する。
方針：単位加群の Hom のチャートを dg Yoneda の全複体同型で送る。
規約：同じ実基礎空間関手を使い、全基点と指定道を維持する。
使われ方：元の coherent bar の評価ホモロジー余錐への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet HomologicalComplex
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial

def DGBarCompactPiChart.postcompose {X : SSet.{u}} [KanComplex X] {n : ℕ}
    {A : Type v} {B : Type w} (c : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart X n A) (e : A ≃ B) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart X n B where
  equiv x := (c.equiv x).trans e
  of_transport p a b h := congrArg e (c.of_transport p a b h)

lemma dgBarCompactPiChart_postcompose_naturality
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] {n : ℕ}
    {A A' B B' : Type v} (c : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart X n A)
    (c' : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart Y n B) (α : A ≃ A') (β : B ≃ B')
    (f : X ⟶ Y) (φ : A → B) (ψ : A' → B')
    (hf : ∀ x a, c'.equiv (f.app _ x) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n f x a) = φ (c.equiv x a))
    (hφ : ∀ a, β (φ a) = ψ (α a)) (x : X _⦋0⦌) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) :
    (c'.postcompose β).equiv (f.app _ x) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n f x a) =
      ψ ((c.postcompose α).equiv x a) :=
  (congrArg β (hf x a)).trans (hφ (c.equiv x a))

variable (R : Type u) [CommRing R] (D : Type v)

/-- 元の加群の実基礎空間値。 -/
def dgBarCompactModuleValueSpace (M : RightModule R PUnit.{1}) : SSet.{max (u + 1) v} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R D).app (Opposite.op ⦋0⦌)
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R
      (RightModule R PUnit.{1})).obj M))))).obj

instance dgBarCompactModuleValueSpace_kan (M : RightModule R PUnit.{1}) :
    KanComplex (dgBarCompactModuleValueSpace R D M) :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject _).obj)

/-- 同じ値を coherent 比較の頂点表示で読む。 -/
def dgBarCompactModuleRawValueSpace (M : RightModule R PUnit.{1}) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoherentUnderlyingValueFunctor R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D)).app (Opposite.op ⦋0⦌)
    (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R)
      (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))).app
        (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M)))))).obj

lemma dgBarCompactModuleRawValueSpace_eq (M : RightModule R PUnit.{1}) :
    dgBarCompactModuleRawValueSpace R D M =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R D).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R
          (RightModule R PUnit.{1})).obj M))))).obj := by
  dsimp only [dgBarCompactModuleRawValueSpace, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoherentUnderlyingValueFunctor]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentNerveVertex_eq_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison_vertex,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUnderlyingValueFunctor_unit]

instance dgBarCompactModuleRawValueSpace_kan (M : RightModule R PUnit.{1}) :
    KanComplex (dgBarCompactModuleRawValueSpace R D M) :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject _).obj)

/-- 同じ線形比較と Yoneda 同型による全基点チャート。 -/
def dgBarCompactModuleRawValuePiChart (M : RightModule R PUnit.{1}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart (dgBarCompactModuleRawValueSpace R D M) n
      ((M.obj (Opposite.op PUnit.unit)).homology (-((n + 1 : ℕ) : ℤ))) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallPiChart R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M) n).postcompose
      (homologyMapIso (dgYonedaIso R PUnit.unit M) (-((n + 1 : ℕ) : ℤ))).toLinearEquiv.toEquiv

/-- 元の加群の native 値の全基点チャート。 -/
def dgBarCompactModuleValuePiChart (M : RightModule R PUnit.{1}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart (dgBarCompactModuleValueSpace R D M) n
      ((M.obj (Opposite.op PUnit.unit)).homology (-((n + 1 : ℕ) : ℤ))) :=
  (dgBarCompactModuleRawValuePiChart R D M n).cast (dgBarCompactModuleRawValueSpace_eq R D M)

/-- 同じ実比較を使う連結成分チャート。 -/
def dgBarCompactModuleRawValuePiZeroChart (M : RightModule R PUnit.{1}) :
    SSet.π₀ (dgBarCompactModuleRawValueSpace R D M) ≃ (M.obj (Opposite.op PUnit.unit)).homology 0 :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactNativeHomSmallPiZeroChart R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M)).trans
      (homologyMapIso (dgYonedaIso R PUnit.unit M) 0).toLinearEquiv.toEquiv

/-- 元の native 値の零次数チャート。 -/
def dgBarCompactModuleValuePiZeroChart (M : RightModule R PUnit.{1}) :
    SSet.π₀ (dgBarCompactModuleValueSpace R D M) ≃ (M.obj (Opposite.op PUnit.unit)).homology 0 :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiZeroChart_cast (dgBarCompactModuleRawValueSpace_eq R D M)
    (dgBarCompactModuleRawValuePiZeroChart R D M)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
