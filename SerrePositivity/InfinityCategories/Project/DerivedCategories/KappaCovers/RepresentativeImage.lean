module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaClosedProjectivePretriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedModuleValuedCommonExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleH0Property
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorTriangulated
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.KST.NonConnective.DGKappaConeInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedStability

/-!
概要：同じ選択代表系の K(D) 内の本質像を三角的対象条件として公開する。
方針：小さい前三角部分圏の完全充満忠実包含と native h/H⁰ 比較を使う。
規約：全同型コピーを選択集合へ追加しない。使われ方：retract の telescope 代表化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u})

def dgKappaCoversUnderlying : _root_.SerrePositivity.DifferentialGraded.DGFunctor R
    {M : ModuleCategory R D // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M} (RightModule R D) :=
  (_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ)).comp (dgConeModuleForget R D)

abbrev dgKappaCoversHoFunctor := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
  (dgKappaCoversUnderlying R D κ))).toFunctor

def dgKappaCoversImage : ObjectProperty (_root_.SerrePositivity.DifferentialGraded.ModuleHomotopyCategory R D) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleH0Property R D (dgKappaCoversHoFunctor R D κ).essImage

lemma dgKappaCoversImage_iff (X : _root_.SerrePositivity.DifferentialGraded.ModuleHomotopyCategory R D) :
    dgKappaCoversImage R D κ X ↔ ∃ M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M ∧
      Nonempty ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).obj M ≅ X) := by
  let E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (RightModule R D)
  constructor
  · rintro ⟨a, ⟨e⟩⟩
    obtain ⟨z, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
    exact ⟨M.val, M.property, ⟨E.functor.mapIso e ≪≫ E.counitIso.app X⟩⟩
  · rintro ⟨M, hM, ⟨e⟩⟩
    let a := HomotopyCategory.mk (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R
      {M : ModuleCategory R D // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M}) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex
      (⟨M, hM⟩ : {M : ModuleCategory R D // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M}))
    exact ⟨a, ⟨E.unitIso.app ((dgKappaCoversHoFunctor R D κ).obj a) ≪≫ E.inverse.mapIso e⟩⟩

instance dgKappaCoversImage_isClosedUnderIsomorphisms :
    (dgKappaCoversImage R D κ).IsClosedUnderIsomorphisms := by
  constructor
  intro X Y e hx
  obtain ⟨M, hM, ⟨i⟩⟩ := (dgKappaCoversImage_iff R D κ X).mp hx
  exact (dgKappaCoversImage_iff R D κ Y).mpr ⟨M, hM, ⟨i ≪≫ e⟩⟩

lemma dgKappaCoversImage_isTriangulated (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular) :
    (dgKappaCoversImage R D κ).IsTriangulated := by
  let C := {M : ModuleCategory R D // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M}
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_small R D κ
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_isDGPretriangulated R D hκ hreg
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated R C
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedModuleValuedFunctorCommon_isExactFunctor.{u, max (u + 1) v, v, 0}
    R C D (dgKappaCoversUnderlying R D κ)
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_ulift (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaCoversUnderlying R D κ)) he
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaCoversUnderlying R D κ)) := by
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isFullyFaithful_of_homIso
    intro M N
    change IsIso (𝟙 _ ≫ 𝟙 _)
    infer_instance
  let : (dgKappaCoversHoFunctor R D κ).Full := hf.toHoFullyFaithful.full
  let : (dgKappaCoversHoFunctor R D κ).CommShift ℤ := inferInstance
  let : (dgKappaCoversHoFunctor R D κ).IsTriangulated := inferInstance
  let : (dgKappaCoversHoFunctor R D κ).essImage.IsTriangulated := inferInstance
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleH0Property_isTriangulated R D (dgKappaCoversHoFunctor R D κ).essImage

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
