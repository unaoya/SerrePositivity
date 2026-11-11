module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.BousfieldUniversalProperty
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalReplacementSaturation
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveInvertedHom

/-!
概要：Bousfield 反射の反転辺は、生成族の局所同値および強飽和生成閉包と一致する。
方針：実局所置換で N の飽和性定理を適用し、反射の写像空間判定で反転辺を同定する。
規約：局所置換・反射・小生成性の追加仮定はない。
使われ方：HTT 5.5.4.15(4) と同じ局所化関手の普遍性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 指定辺集合の局所対象への反射では、単位による局所性と元の局所性が一致する。 -/
lemma reflective_isLocal_iff_localObject
    {C : SSet.{u}} [Quasicategory C] (W : Set (C _⦋1⦌))
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory C (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W)) (z : C _⦋0⦌) :
    r.IsLocal z ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W z := by
  constructor
  · intro hz
    obtain ⟨y, ⟨e⟩⟩ := (r.isLocal_iff_essentialImage z).mp hz
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalObject_iff_of_vertexIso W e).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex y)
  · intro hz
    apply r.isLocal_inclusion ⟨z, ?_⟩
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    simpa only [hα, op_id, CategoryTheory.Functor.map_id_apply] using hz

/-- 元の局所同値は、構成した Bousfield 局所化関手が反転する元の辺と一致する。 -/
lemma bousfield_localEquivalences_eq_invertedEdges
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences (Set.range edges) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor hC edges) := by
  ext s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalEquivalenceHom (Set.range edges)
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s)) ↔
    IsIso ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldReflection hC edges).reflector).toFunctor.map
      (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s)))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.reflective_isIso_map_iff_localHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldReflection hC edges)]
  constructor
  · intro hs z hz
    exact hs z ((reflective_isLocal_iff_localObject _ _ z).mp hz)
  · intro hs z hz
    exact hs z ((reflective_isLocal_iff_localObject _ _ z).mpr hz)

/-- 構成済みの実局所置換から、強飽和生成閉包は元の局所同値全体と一致する。 -/
lemma bousfield_generatedEdges_eq_localEquivalences
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences (Set.range edges) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.stronglySaturatedClosure_eq_localEquivalences_of_localReplacements _ hC.hasSmallColimits
  intro x
  obtain ⟨y, e, he, hy⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_bousfieldLocalReplacement hC edges x
  exact ⟨y, e.toTruncated, he, hy⟩

/-- HTT 5.5.4.15(4)：強飽和生成閉包は、同じ反射が反転する辺全体である。 -/
lemma bousfield_generatedEdges_eq_invertedEdges
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor hC edges) :=
  (bousfield_generatedEdges_eq_localEquivalences hC edges).trans
    (bousfield_localEquivalences_eq_invertedEdges hC edges)

/-- 同じ構成した全関手は、強飽和生成閉包について全標的での局所化普遍性を持つ。 -/
lemma bousfieldLocalizationFunctor_isLocalization_generatedEdges
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor hC edges) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges) := by
  rw [bousfield_generatedEdges_eq_invertedEdges hC edges]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor_isLocalization_invertedEdges hC edges

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
