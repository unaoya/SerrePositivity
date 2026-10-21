module

public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
概要：可換正方形の両側が準同型なら、同じ正方形の cone 射も準同型である。
方針：標準導来圏の実 cone 三角形へ移し、三角形の二射の可逆性を使う。
規約：モデル圏の仮定は不要。使われ方：Postnikov 層と実 kernel の cone 比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory CochainComplex HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

lemma cochainConeMap_quasiIso {M K M' K' : Complex R}
    (i : M ⟶ K) (i' : M' ⟶ K') (a : M ⟶ M') (b : K ⟶ K')
    (h : i ≫ b = a ≫ i') (ha : QuasiIso a) (hb : QuasiIso b) :
    QuasiIso (mappingCone.map i i' a b h) := by
  have := ha
  have := hb
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mp
  exact CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂
    (DerivedCategory.Q.mapTriangle.map (mappingCone.triangleMap i i' a b h))
    (DerivedCategory.mappingCone_triangle_distinguished _)
    (DerivedCategory.mappingCone_triangle_distinguished _)
    (by change IsIso (DerivedCategory.Q.map a); infer_instance)
    (by change IsIso (DerivedCategory.Q.map b); infer_instance)

end SerrePositivity.KST.LocalizingInvariants
