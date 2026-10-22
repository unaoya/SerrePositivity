module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassSourceHomology
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroExtensionLayerMap

/-!
概要：二切断候補の同じ五つの実拡大模型の H⁻² を、元の係数の H⁻³ と実同型で同定する。
方針：構成した共通源の二次数の消滅を、既存の実層ホモロジー同型へ渡す。
規約：元の係数と符号を保ち、消滅を追加入力しない。使われ方：実候補の π₂ 作用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def sourceLayerIso : (d.sourceModel R).X.homology (-2) ≅ (d.denominatorLayer R).X.homology (-3) :=
  SquareZeroExtension.layerHomologyIso (d.denominatorLayer R) (d.sourceClass R) (-2)
    (d.classSource_homology_zero R _ (by omega)) (d.classSource_homology_zero R _ (by omega))

def imageLayerIso : (d.imageModel R).X.homology (-2) ≅ (d.numeratorLayer R).X.homology (-3) :=
  SquareZeroExtension.layerHomologyIso (d.numeratorLayer R) (d.imageClass R) (-2)
    (d.classSource_homology_zero R _ (by omega)) (d.classSource_homology_zero R _ (by omega))

def targetLayerIso : (d.targetModel R).X.homology (-2) ≅ (d.numeratorLayer R).X.homology (-3) :=
  SquareZeroExtension.layerHomologyIso (d.numeratorLayer R) (d.targetClass R) (-2)
    (d.classSource_homology_zero R _ (by omega)) (d.classSource_homology_zero R _ (by omega))

def pathLayerIso : (d.pathModel R).X.homology (-2) ≅ (d.numeratorLayer R).X.homology (-3) :=
  SquareZeroExtension.layerHomologyIso (d.numeratorLayer R) 
    (MappingPath.target R (d.imageClass R)) (-2)
    (d.pathSource_homology_zero R _ (by omega)) (d.pathSource_homology_zero R _ (by omega))

def targetComposedLayerIso :
    (d.targetComposedModel R).X.homology (-2) ≅ (d.numeratorLayer R).X.homology (-3) :=
  SquareZeroExtension.layerHomologyIso (d.numeratorLayer R) 
    (𝟙 (d.classSource R) ≫ d.targetClass R) (-2)
    (d.classSource_homology_zero R _ (by omega)) (d.classSource_homology_zero R _ (by omega))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
