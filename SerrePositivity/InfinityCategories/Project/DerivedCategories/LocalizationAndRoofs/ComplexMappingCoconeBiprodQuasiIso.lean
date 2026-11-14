module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexMappingCoconeBiprodExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.ComplexShortExactQuasiIso
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
/-!
概要：第二成分が準同型なら、二成分差の mapping cocone の実第一射影も準同型。
方針：実短完全列の左 cocone の acyclic 性を、同じ第二鎖写像の準同型性から得る。
規約：非有界複体・任意可換基礎環。使われ方：一般出力分解 Hom の実比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex
/-- 実第二成分が準同型なら、同じ cocone の実第一射影も準同型。 -/
lemma complexMappingCoconeBiprodProjection_quasiIso {R : Type u} [CommRing R]
    {K L T : Complex R} (a : K ⟶ T) (b : L ⟶ T) (hb : QuasiIso b) :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodProjection a b) := by
  have hc : (mappingCocone b).Acyclic :=
    SerrePositivity.cochainAcyclic_shift ((complex_quasiIso_iff_acyclic_cone R b).mp hb) (-1)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexShortExact_quasiIso_projection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodShortComplex a b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodShortComplex_shortExact a b) hc
/-- 実差写像の表示を指定したまま、同じ実射影の準同型性を得る。 -/
lemma complexMappingCoconeProjection_quasiIso_of_eq {R : Type u} [CommRing R]
    {K L T : Complex R} (d : K ⊞ L ⟶ T) (a : K ⟶ T) (b : L ⟶ T)
    (hd : d = biprod.desc a b) (hb : QuasiIso b) :
    QuasiIso (mappingCocone.fst d ≫ (biprod.fst : K ⊞ L ⟶ K)) := by
  subst d
  exact complexMappingCoconeBiprodProjection_quasiIso a b hb
end SerrePositivity.InfinityCategories.Project.DerivedCategories
