module

public import SerrePositivity.KST.LocalizingInvariants.ProInverseAfter
public import SerrePositivity.KST.LocalizingInvariants.ProModuleReflection
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageLayerFunctor

/-!
概要：元の整数次数の群の pro 同型から、任意の深さ以降の実線形ホモロジー逆を選ぶ。
方針：群の逆の線形性を既存の二段補正で回収し、元の遷移で深さを揃える。
規約：双加群の逆とは扱わない。使われ方：元の π₂ 逆を roof の係数へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  (j : ℤ) (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R j)))

include hf in
lemma nonpositiveHomologyMap_isProIso :
    IsProIso (f.map (nonpositiveAlgebraHomologyFunctor R (-j))) :=
  TowerDiagram.proIso_of_module_groups R _ hf

include hf in
lemma exists_nonpositiveHomologyInverse_after (i bound : ℕ) :
    ∃ m, ∃ hi : i ≤ m, bound ≤ m ∧
      ∃ r : (B.obj m).obj.X.homology (-j) ⟶ (A.obj i).obj.X.homology (-j),
        homologyMap (f.app m).hom.hom (-j) ≫ r =
          homologyMap (A.transition hi).hom.hom (-j) ∧
        r ≫ homologyMap (f.app i).hom.hom (-j) =
          homologyMap (B.transition hi).hom.hom (-j) :=
  TowerDiagram.exists_inverse_after _ (nonpositiveHomologyMap_isProIso R f j hf) i bound

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
