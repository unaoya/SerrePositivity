module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCylinder
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionPushoutProduct

/-!
概要：単射である前合成の同値条件だけから関手による保存を検出する。
方針：可逆な写像円柱の二つの包含と収縮に二対三則を使う。
規約：モデル構造の補題としてではなく、構成済みの因子分解から直接示す。
使われ方：Kerodon §4.6.2（Tag 01HM） の補助構成による同値の保存。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：単射の前合成の同値条件を保存する関手は全ての前合成の同値条件を保存する。
方針：写像円柱の二つの単射の保存から収縮の保存を二対三則で得る。
規約：関手の極限・余極限の保存は要求しない。
使われ方：Kerodon §4.6.2（Tag 01HM） の写像円柱による同値の検出。 -/
lemma isPrecompositionEquivalence_map_of_mono (F : SSet.{u} ⥤ SSet.{u})
    (hF : ∀ {A B : SSet.{u}} (i : A ⟶ B) [Mono i],
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (F.map i))
    {A B : SSet.{u}} {f : A ⟶ B} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (F.map f) := by
  let s : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinder f :=
    pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A false) f
  have : Mono s := Adhesive.mono_of_isPushout_of_mono_left (IsPushout.of_hasPushout _ _)
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence s :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_equivalenceCylinderEndpoint A false).of_isPushout
      (IsPushout.of_hasPushout _ _)
  have hsr : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderOut f = 𝟙 B := pushout.inr_desc _ _ _
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderOut f)) := by
    apply (hF s hs).cancel_left
    rw [← F.map_comp, hsr, F.map_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id _
  have hi := hF (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn f)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_iff_equivalenceMappingCylinderIn f).mp hf)
  have h := hi.comp hr
  rwa [← F.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceMappingCylinderIn_out] at h

/-- 概要：前合成の同値条件の関手による保存は単射上で検査すれば十分。
方針：全ての射に関する条件の制限と写像円柱による拡張を組み合わせる。
規約：両方の条件で単体集合の quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の関手による比較の保存。 -/
lemma preservesPrecompositionEquivalences_iff_mono (F : SSet.{u} ⥤ SSet.{u}) :
    (∀ {A B : SSet.{u}} (f : A ⟶ B),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (F.map f)) ↔
    (∀ {A B : SSet.{u}} (f : A ⟶ B) [Mono f],
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (F.map f)) :=
  ⟨fun h _ _ f _ hf ↦ h f hf,
    fun h _ _ _ hf ↦ isPrecompositionEquivalence_map_of_mono F h hf⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
