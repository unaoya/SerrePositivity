module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorClassSourceHomology
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroExtensionLayerMap

/-!
概要：次段切断候補の同じ五つの実拡大模型の H⁻⁽ⁿ⁺¹⁾ を、元の係数の H⁻⁽ⁿ⁺²⁾ と実同型で同定する。
方針：構成した共通源の二次数の消滅を、既存の実層ホモロジー同型へ渡す。
規約：元の係数と符号を保ち、消滅を追加入力しない。使われ方：実候補の πₙ₊₁ 作用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

def sourceLayerIso : (d.sourceModel R).X.homology (-(n + 1)) ≅ (d.denominatorLayer R).X.homology (-(n + 1) - 1) :=
  SquareZeroExtension.layerHomologyIso (d.denominatorLayer R) (d.sourceClass R) (-(n + 1))
    (d.classSource_homology_zero R _ (by omega)) (d.classSource_homology_zero R _ (by omega))

def imageLayerIso : (d.imageModel R).X.homology (-(n + 1)) ≅ (d.numeratorLayer R).X.homology (-(n + 1) - 1) :=
  SquareZeroExtension.layerHomologyIso (d.numeratorLayer R) (d.imageClass R) (-(n + 1))
    (d.classSource_homology_zero R _ (by omega)) (d.classSource_homology_zero R _ (by omega))

def targetLayerIso : (d.targetModel R).X.homology (-(n + 1)) ≅ (d.numeratorLayer R).X.homology (-(n + 1) - 1) :=
  SquareZeroExtension.layerHomologyIso (d.numeratorLayer R) (d.targetClass R) (-(n + 1))
    (d.classSource_homology_zero R _ (by omega)) (d.classSource_homology_zero R _ (by omega))

def pathLayerIso : (d.pathModel R).X.homology (-(n + 1)) ≅ (d.numeratorLayer R).X.homology (-(n + 1) - 1) :=
  SquareZeroExtension.layerHomologyIso (d.numeratorLayer R)
    (MappingPath.target R (d.imageClass R)) (-(n + 1))
    (d.pathSource_homology_zero R _ (by omega)) (d.pathSource_homology_zero R _ (by omega))

def targetComposedLayerIso :
    (d.targetComposedModel R).X.homology (-(n + 1)) ≅ (d.numeratorLayer R).X.homology (-(n + 1) - 1) :=
  SquareZeroExtension.layerHomologyIso (d.numeratorLayer R)
    (𝟙 (d.classSource R) ≫ d.targetClass R) (-(n + 1))
    (d.classSource_homology_zero R _ (by omega)) (d.classSource_homology_zero R _ (by omega))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
