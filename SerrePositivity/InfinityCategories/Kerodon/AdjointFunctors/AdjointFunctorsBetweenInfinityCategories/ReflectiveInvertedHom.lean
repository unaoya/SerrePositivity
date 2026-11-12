module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ReflectiveLocality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalEquivalences
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveLocalization
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：反射の局所対象と反転する元の辺を写像空間で特徴づける。
方針：元の単位の自然性と局所性を使い、反転した射の可逆性を全忠実な包含で反映する。
規約：与えられた反射の性質であり存在定理ではない。使われ方：HTT 5.5.4.2(1)・(2)。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
noncomputable section
variable {X : SSet.{u}} [Quasicategory X] {P : X _⦋0⦌ → Prop}
/-- 反射が反転する元の hX の射に対して、反射の全局所対象は局所。 -/
lemma reflective_invertedHom_isLocal {x y : X _⦋0⦌}
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory X P)
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y)
    (hf : IsIso ((hoFunctor.map r.reflector).toFunctor.map f))
    {z : X _⦋0⦌} (hz : r.IsLocal z) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom f z := by
  let i := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι
  have : IsIso ((hoFunctor.map r.localization).toFunctor.map f) := by
    change IsIso ((hoFunctor.map (r.reflector ≫ i)).toFunctor.map f)
    rw [Functor.map_comp]
    exact inferInstanceAs (IsIso ((hoFunctor.map i).toFunctor.map
      ((hoFunctor.map r.reflector).toFunctor.map f)))
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.functorHomEvaluate_naturality r.unit f
  have hid : (hoFunctor.map (𝟙 X)).toFunctor = 𝟭 (hoFunctor.obj X) := by
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hm : (hoFunctor.map (𝟙 X)).toFunctor.map f = f := by
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, Cat.Hom.id_map,
      CategoryTheory.Functor.id_map] using CategoryTheory.Functor.congr_hom hid f
  rw [hm] at h
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit x ≫ (hoFunctor.map r.localization).toFunctor.map f) z :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_comp _ _ z (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectiveUnit_isLocalForHom r hz x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_of_isIso _ z)
  have hc' : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit y) z := h ▸ hc
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_cancel_right _ _ z (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectiveUnit_isLocalForHom r hz y) hc'
/-- 指定端点を持つ辺の局所性と、同じ元の一次単体による局所性は一致する。 -/
lemma isLocalForHom_homMk_iff_edgeOfSimplex {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) (z : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk e) z ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e.edge)) z := by
  rcases e with ⟨s, hx, hy⟩
  subst x y
  rfl

/-- 反射の局所対象は元の反射が反転する辺集合に対する局所対象と一致する。 -/
@[kerodon 06TB]
lemma reflective_isLocal_iff_invertedEdges (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory X P) (z : X _⦋0⦌) :
    r.IsLocal z ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector) z := by
  constructor
  · intro hz s hs
    apply reflective_invertedHom_isLocal r _ _ hz
    exact hs
  · intro hz
    apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflective_isLocal_iff_unit_local r z).mpr
    intro x
    let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy r.unit) x).toTruncated
    have he := hz e.edge (r.unitComponent_mem_invertedEdges x)
    have hl := (isLocalForHom_homMk_iff_edgeOfSimplex e z).mpr he
    simpa only [e, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_component, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent] using hl

/-- 反射はちょうど全ての局所対象への写像空間が検出する元の射を反転する。 -/
lemma reflective_isIso_map_iff_localHom {x y : X _⦋0⦌}
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory X P)
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) :
    IsIso ((hoFunctor.map r.reflector).toFunctor.map f) ↔
      ∀ z : X _⦋0⦌, r.IsLocal z → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom f z := by
  constructor
  · intro hf z hz
    exact reflective_invertedHom_isLocal r f hf hz
  · intro hf
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.functorHomEvaluate_naturality r.unit f
    have hid : (hoFunctor.map (𝟙 X)).toFunctor = 𝟭 (hoFunctor.obj X) := by
      rw [CategoryTheory.Functor.map_id]
      rfl
    have hm : (hoFunctor.map (𝟙 X)).toFunctor.map f = f := by
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, Cat.Hom.id_map,
        CategoryTheory.Functor.id_map] using CategoryTheory.Functor.congr_hom hid f
    rw [hm] at h
    have hL (z : X _⦋0⦌) (hz : r.IsLocal z) :
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom ((hoFunctor.map r.localization).toFunctor.map f) z := by
      have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit y) z :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_comp _ _ z (hf z hz) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectiveUnit_isLocalForHom r hz y)
      have hc' : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit x ≫ (hoFunctor.map r.localization).toFunctor.map f) z :=
        h.symm ▸ hc
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_cancel_left _ _ z (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectiveUnit_isLocalForHom r hz x) hc'
    have hLf : IsIso ((hoFunctor.map r.localization).toFunctor.map f) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isIso_of_isLocalForHom_source_target _
        (hL _ (r.isLocal_localization x)) (hL _ (r.isLocal_localization y))
    have hmap : IsIso ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι).toFunctor.map
        ((hoFunctor.map r.reflector).toFunctor.map f)) := by
      change IsIso ((hoFunctor.map r.reflector ≫ hoFunctor.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι).toFunctor.map f)
      rw [← Functor.map_comp]
      exact hLf
    exact r.inclusion_fullyFaithful.toHoFullyFaithful.isIso_of_isIso_map _

/-- 反射の反転辺集合に対する S-equivalence は元の反射が反転する hX の射。 -/
lemma reflective_localEquivalenceHom_iff {x y : X _⦋0⦌}
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory X P)
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalEquivalenceHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector) f ↔
      IsIso ((hoFunctor.map r.reflector).toFunctor.map f) := by
  rw [reflective_isIso_map_iff_localHom]
  constructor
  · intro h z hz
    exact h z ((reflective_isLocal_iff_invertedEdges r z).mp hz)
  · intro h z hz
    exact h z ((reflective_isLocal_iff_invertedEdges r z).mpr hz)

/-- 元の反射が反転する辺集合は S-equivalence による拡大で不変。 -/
@[kerodon 06TB]
lemma reflective_localEquivalences_eq (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory X P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector := by
  ext s
  exact reflective_localEquivalenceHom_iff r
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s))

end
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
