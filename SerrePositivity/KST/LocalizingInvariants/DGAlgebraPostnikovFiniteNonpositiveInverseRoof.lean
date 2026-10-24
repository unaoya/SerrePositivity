module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovBoundedRightInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeRightRoofRetarget
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovFiniteDiagonalLeftReflection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveInverseRoofOfLeftPath

/-!
概要：任意の有限切断で、元の右逆と対角の右逆から厳密な左三角形も構成する。
方針：対角右逆を元の左欠損に適用し、cell 細分と非正次数化で反映する。
規約：元の右経路を保持する。使われ方：有限 Postnikov 帰納の後続段。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] (cutoff : ℤ)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m k : ℕ} {him : i ≤ m} {hmk : m ≤ k}
  (q : NativeRightInverseRoof R ((postnikovFiniteNonpositiveDiagonal R cutoff f).map
    (nonpositiveInclusion R)) i m him)
  (c : NativeRightInverseRoof R (f.map (postnikovFunctor R cutoff)) m k hmk)

def postnikovFiniteInverseRoofOfDiagonalRight :
    NonpositiveInverseRoof R (f.map (postnikovFunctor R cutoff)) i k (him.trans hmk) := by
  have : ((A.map (postnikovFunctor R cutoff)).obj k).X.IsStrictlyLE 0 :=
    postnikov_nonpositive R (A.obj k).obj cutoff
  have : ((B.map (postnikovFunctor R cutoff)).obj k).X.IsStrictlyLE 0 :=
    postnikov_nonpositive R (B.obj k).obj cutoff
  let c' := c.retarget R him
  let T := c.nonpositiveSource R
  let p := cellAugmentation R T ≫ c.sourceProjection R
  let a : cellResolution R T ⟶ c'.roof.apex := cellAugmentation R T ≫ c.sourceLift R
  have hp : ∀ n : ℤ, Function.Surjective (p.hom.f n) := fun n =>
    (c.sourceProjection_surjective R n).comp (cellAugmentation_surjective R T n)
  have hq : QuasiIso p.hom := quasiIso_comp _ _
    (hφ := cellAugmentation_quasiIso R T) (hφ' := c.sourceProjection_quasiIso R)
  have hd : a ≫ c'.roof.denominator = p ≫ postnikovMap R (f.app k).hom cutoff := by
    change (cellAugmentation R T ≫ c.sourceLift R) ≫ c.roof.denominator = _
    rw [Category.assoc, c.sourceLift_denominator R, ← Category.assoc]
    rfl
  let w := postnikovFiniteDiagonalLeftReflection R cutoff f q c
  let w' : Path.Witness R (a ≫ c'.roof.numerator)
      (p ≫ postnikovMap R (A.transition (him.trans hmk)).hom cutoff) :=
    ⟨w.hom,
      w.source_eq.trans (by
        change cellAugmentation R T ≫ ((c.sourceLift R ≫ c.roof.numerator) ≫
          postnikovMap R (A.transition him).hom cutoff) =
          (cellAugmentation R T ≫ c.sourceLift R) ≫
            (c.roof.numerator ≫ postnikovMap R (A.transition him).hom cutoff)
        simp only [Category.assoc]),
      w.target_eq.trans (Category.assoc _ _ _).symm⟩
  exact c'.nonpositiveOfLeftPath R p hp hq a hd w'

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
