module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeRightInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveNativeInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverSurjective

/-!
概要：任意の実全射準同型細分上の厳密左三角形を、非正次数逆 roof へ正規化する。
方針：頂点と源へ同じ cover を適用し、元の二脚と実右経路を保つ。
規約：細分を反復 cell 分解に限定しない。使われ方：対角反映後の厳密化。
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
variable (R : Type u) [CommRing R] {X Y : Tower (Mon (Complex R))}
  {f : LevelHom X Y} {i m : ℕ} {hi : i ≤ m} (c : NativeRightInverseRoof R f i m hi)
  [(X.obj m).X.IsStrictlyLE 0] [(Y.obj m).X.IsStrictlyLE 0]
  {T : Mon (Complex R)} (e : T ⟶ X.obj m)
  (he : ∀ n : ℤ, Function.Surjective (e.hom.f n)) (hq : QuasiIso e.hom)
  (a : T ⟶ c.roof.apex) (ha : a ≫ c.roof.denominator = e ≫ f.app m)
  (hb : a ≫ c.roof.numerator = e ≫ X.transition hi)

def NativeRightInverseRoof.nonpositiveOfStrictSource : NonpositiveInverseRoof R f i m hi := by
  let q := c.roof.nonpositiveNormalization R
  let s := connectiveCoverInclusion R T ≫ e
  let l := connectiveCoverMap R a
  have hl : l ≫ connectiveCoverInclusion R c.roof.apex = connectiveCoverInclusion R T ≫ a :=
    (connectiveCoverCounit R).naturality a
  refine ⟨q, c.roof.nonpositiveNormalization_apex R, connectiveCover R T,
    coverComplex_nonpositive R T, s, ?_, ?_, l, ?_, ?_, ?_⟩
  · apply HomologicalComplex.epi_of_epi_f
    intro n
    apply (ModuleCat.epi_iff_surjective _).2
    exact connectiveCoverInclusion_comp_surjective R e he hq n
  · exact connectiveCoverInclusion_comp_quasiIso R e hq
  · change l ≫ (connectiveCoverInclusion R c.roof.apex ≫ c.roof.denominator) = s ≫ f.app m
    rw [← Category.assoc, hl, Category.assoc, ha, ← Category.assoc]
  · change l ≫ (connectiveCoverInclusion R c.roof.apex ≫ c.roof.numerator) = s ≫ X.transition hi
    rw [← Category.assoc, hl, Category.assoc, hb, ← Category.assoc]
  · let w := c.rightPath.precomp (connectiveCoverInclusion R c.roof.apex)
    exact ⟨w.hom, w.source_eq.trans (Category.assoc _ _ _).symm,
      w.target_eq.trans (Category.assoc _ _ _).symm⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
