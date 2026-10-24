module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassSourceModel

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorClassSourceHomology

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
  PostnikovSuccessorClassInverseData.sourceBaseComparison
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceBaseComparison_quasiIso : QuasiIso (d.sourceBaseComparison R).hom :=
  PostnikovSuccessorClassInverseData.sourceBaseComparison_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma classSource_homology_zero (z : ℤ) (hz : z < -1) :
    IsZero ((d.classSource R).X.homology z) :=
  PostnikovSuccessorClassInverseData.classSource_homology_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (z := z) (hz := hz)

lemma pathSource_homology_zero (z : ℤ) (hz : z < -1) :
    IsZero ((MappingPath.algebra R (d.imageClass R)).X.homology z) :=
  PostnikovSuccessorClassInverseData.pathSource_homology_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (z := z) (hz := hz)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
