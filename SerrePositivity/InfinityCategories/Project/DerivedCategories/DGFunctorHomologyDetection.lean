module
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
/-!
概要：H⁰ の同じ実 Hom 写像の全単射性から、元の Hom 鎖写像の H⁰ 準同型性を得る。
方針：cycle の標準ホモロジー類の関手自然性を全単射と共役する。
規約：全次数の準同型性はまだ主張しない。使われ方：β5 の Morita 比較の各 shift。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory HomologicalComplex DifferentialGraded
/-- H⁰ の実 Hom 写像が全単射なら、元の Hom 鎖写像は次数零で準同型。 -/
lemma dgFunctor_quasiIsoAt_zero_of_ho_map_bijective {R : Type u} [CommRing R]
    {D : Type v} [DGCategory R D] {E : Type w} [DGCategory R E]
    (F : DGFunctor R D E) (x y : ClosedCategory R D)
    (h : Function.Bijective (F.onHomotopy.map
      (X := (toHomotopy R D).obj x) (Y := (toHomotopy R D).obj y))) :
    QuasiIsoAt (F.map x y) 0 := by
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  let e := homotopyHomologyEquiv R D x y
  let e' := homotopyHomologyEquiv R E (F.onClosed.obj x) (F.onClosed.obj y)
  have he : (fun z => homologyMap (F.map x y) 0 z) =
      fun z => e' (F.onHomotopy.map (e.symm z)) := by
    funext z
    simpa only [e, e', Equiv.apply_symm_apply] using
      (F.homotopyHomologyEquiv_map_naturality (e.symm z)).symm
  exact (congrArg Function.Bijective he).mpr (e'.bijective.comp (h.comp e.symm.bijective))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
