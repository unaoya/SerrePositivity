module

public import SerrePositivity.KST.LocalizingInvariants.CochainDegreeBounds
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathFunctor

/-!
概要：非正次数源から非負次数標的への実経路は、端点と同じ定数経路に厳密に一致する。
方針：負一次 cochain の零性で両端を等しくし、両端と比較 cochain の一意性を使う。
規約：元の実経路射を保持。使われ方：零切断へ送った経路の相対性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)}
  [A.X.IsStrictlyLE 0] [B.X.IsStrictlyGE 0]

lemma Witness.eq_of_degree_bounds {f g : A ⟶ B} (w : Witness R f g) : f = g := by
  apply Mon.Hom.ext
  exact cochainHom_eq_of_homotopy_bounds w.chainHomotopy

lemma map_to_discrete_constant (a : A ⟶ algebra R B) : a = (a ≫ source R B) ≫ diagonal R B := by
  have he : a ≫ source R B = a ≫ target R B :=
    (Witness.eq_of_degree_bounds R (Witness.mk a rfl rfl))
  have hs : a ≫ source R B = ((a ≫ source R B) ≫ diagonal R B) ≫ source R B := by
    simp only [Category.assoc, diagonal_source, Category.comp_id]
  have ht : a ≫ target R B = ((a ≫ source R B) ≫ diagonal R B) ≫ target R B := by
    simpa only [Category.assoc, diagonal_target, Category.comp_id] using he.symm
  apply Mon.Hom.ext
  apply chain_ext R B
  · exact congrArg Mon.Hom.hom hs
  · exact congrArg Mon.Hom.hom ht
  · exact (cochainDegree_eq_zero_of_bounds 0 0 (-1) (by omega) _).trans
      (cochainDegree_eq_zero_of_bounds 0 0 (-1) (by omega) _).symm

lemma Witness.hom_eq_constant {f g : A ⟶ B} (w : Witness R f g) :
    w.hom = f ≫ diagonal R B :=
  (map_to_discrete_constant R w.hom).trans (congrArg (fun t => t ≫ diagonal R B) w.source_eq)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
