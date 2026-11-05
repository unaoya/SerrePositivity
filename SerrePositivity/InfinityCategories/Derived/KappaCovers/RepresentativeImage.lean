module
public import SerrePositivity.InfinityCategories.Derived.DGKappaClosedProjectivePretriangulated
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedModuleValuedCommonExact
public import SerrePositivity.InfinityCategories.Derived.DGModuleH0Property
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorTriangulated
public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.KST.NonConnective.DGKappaConeInput
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedStability

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u})

def dgKappaCoversUnderlying : DGFunctor R
    {M : ModuleCategory R D // dgKappaClosedProjectiveObjects R D κ M} (RightModule R D) :=
  (dgFullSubcategoryInclusion R (ModuleCategory R D)
    (dgKappaClosedProjectiveObjects R D κ)).comp (dgConeModuleForget R D)

abbrev dgKappaCoversHoFunctor := (hoFunctor.map (dgNerve.map
  (dgKappaCoversUnderlying R D κ))).toFunctor

def dgKappaCoversImage : ObjectProperty (ModuleHomotopyCategory R D) :=
  dgModuleH0Property R D (dgKappaCoversHoFunctor R D κ).essImage

lemma dgKappaCoversImage_iff (X : ModuleHomotopyCategory R D) :
    dgKappaCoversImage R D κ X ↔ ∃ M : ModuleCategory R D,
      dgKappaClosedProjectiveObjects R D κ M ∧
      Nonempty ((moduleToHomotopy R D).obj M ≅ X) := by
  let E := dgStableHomotopyEquivalence R (RightModule R D)
  constructor
  · rintro ⟨a, ⟨e⟩⟩
    obtain ⟨z, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective z
    exact ⟨M.val, M.property, ⟨E.functor.mapIso e ≪≫ E.counitIso.app X⟩⟩
  · rintro ⟨M, hM, ⟨e⟩⟩
    let a := HomotopyCategory.mk (X := dgNerve R
      {M : ModuleCategory R D // dgKappaClosedProjectiveObjects R D κ M}) (Simplex.vertex
      (⟨M, hM⟩ : {M : ModuleCategory R D // dgKappaClosedProjectiveObjects R D κ M}))
    exact ⟨a, ⟨E.unitIso.app ((dgKappaCoversHoFunctor R D κ).obj a) ≪≫ E.inverse.mapIso e⟩⟩

instance dgKappaCoversImage_isClosedUnderIsomorphisms :
    (dgKappaCoversImage R D κ).IsClosedUnderIsomorphisms := by
  constructor
  intro X Y e hx
  obtain ⟨M, hM, ⟨i⟩⟩ := (dgKappaCoversImage_iff R D κ X).mp hx
  exact (dgKappaCoversImage_iff R D κ Y).mpr ⟨M, hM, ⟨i ≪≫ e⟩⟩

lemma dgKappaCoversImage_isTriangulated (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular) :
    (dgKappaCoversImage R D κ).IsTriangulated := by
  let C := {M : ModuleCategory R D // dgKappaClosedProjectiveObjects R D κ M}
  let := dgKappaClosedProjectiveObjects_small R D κ
  let := dgKappaClosedProjectiveObjects_isDGPretriangulated R D hκ hreg
  let := dgNerve_isStable_of_pretriangulated R C
  have he := dgPretriangulatedModuleValuedFunctorCommon_isExactFunctor.{u, max (u + 1) v, v, 0}
    R C D (dgKappaCoversUnderlying R D κ)
  let := isExactFunctor_of_ulift (dgNerve.map (dgKappaCoversUnderlying R D κ)) he
  have hf : IsFullyFaithful (dgNerve.map (dgKappaCoversUnderlying R D κ)) := by
    apply dgNerve_map_isFullyFaithful_of_homIso
    intro M N
    change IsIso (𝟙 _ ≫ 𝟙 _)
    infer_instance
  let : (dgKappaCoversHoFunctor R D κ).Full := hf.toHoFullyFaithful.full
  let : (dgKappaCoversHoFunctor R D κ).CommShift ℤ := inferInstance
  let : (dgKappaCoversHoFunctor R D κ).IsTriangulated := inferInstance
  let : (dgKappaCoversHoFunctor R D κ).essImage.IsTriangulated := inferInstance
  exact dgModuleH0Property_isTriangulated R D (dgKappaCoversHoFunctor R D κ).essImage

end SerrePositivity.InfinityCategories
