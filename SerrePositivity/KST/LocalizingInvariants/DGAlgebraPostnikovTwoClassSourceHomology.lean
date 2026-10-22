module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassSourceModel

/-!
概要：二切断候補の同じ共通源と mapping-path 源の H⁻³・H⁻² 消滅を実証する。
方針：元の τ₁ 分母と cell augmentation の準同型で、元の有限切断の消滅を移す。
規約：消滅を追加入力しない。使われ方：候補の実係数への層ホモロジー同定。
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

def sourceBaseComparison : d.classSource R ⟶ postnikov R (B.obj d.layerInverse.zero.stage).obj 1 :=
  d.sourceCellMap R ≫ cellAugmentation R (postnikov R (B.obj d.layerInverse.zero.stage).obj 1)

lemma sourceBaseComparison_quasiIso : QuasiIso (d.sourceBaseComparison R).hom :=
  quasiIso_comp _ _ (hφ := d.sourceCellMap_quasiIso R) (hφ' := cellAugmentation_quasiIso R _)

lemma classSource_homology_zero (z : ℤ) (hz : z < -1) :
    IsZero ((d.classSource R).X.homology z) := by
  have := d.sourceBaseComparison_quasiIso R
  have := postnikov_lowerBound R (B.obj d.layerInverse.zero.stage).obj 1
  exact ((postnikov R (B.obj d.layerInverse.zero.stage).obj 1).X.isZero_of_isGE (-1) z hz).of_iso
    (asIso (homologyMap (d.sourceBaseComparison R).hom z))

lemma pathSource_homology_zero (z : ℤ) (hz : z < -1) :
    IsZero ((MappingPath.algebra R (d.imageClass R)).X.homology z) := by
  have := MappingPath.projection_quasiIso R (d.imageClass R)
  exact (d.classSource_homology_zero R z hz).of_iso
    (asIso (homologyMap (MappingPath.projection R (d.imageClass R)).hom z))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
