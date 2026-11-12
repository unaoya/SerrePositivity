module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveUnitInvertible
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：反射に関する局所対象は包含の本質的な像。
方針：包含上の単位の可逆性を成分へ移し、単位の自然性で同型不変性を示す。
規約：元の頂点条件 P の同型不変性は不要。
使われ方：B2 の局所対象の記述と反射的局所化の普遍性。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：h Fun の二胞体の成分は h 圏の射に自然。
方針：対応する自然変換の自然性を成分評価の一致で書き換える。
規約：標的だけを quasicategory とする。
使われ方：反射単位の可逆性の同型不変性。 -/
lemma functorHomEvaluate_naturality {A X : SSet.{u}} [Quasicategory X]
    {U V : A ⟶ X} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) {x y : A _⦋0⦌}
    (γ : (HomotopyCategory.mk x : hoFunctor.obj A) ⟶ HomotopyCategory.mk y) :
    (hoFunctor.map U).toFunctor.map γ ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α y =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α x ≫ (hoFunctor.map V).toFunctor.map γ := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.functorCellToNatTrans α).naturality γ
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorCellToNatTrans_app_eq_evaluate, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorCellToNatTrans_app_eq_evaluate] at h
  exact h

namespace ReflectiveSubcategory
variable {X : SSet.{u}} [Quasicategory X] {P : X _⦋0⦌ → Prop}
variable (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory X P)

/-- 概要：包含の像の頂点は局所対象。
方針：包含上の単位の h Fun 全体の可逆性を評価し、前合成の成分公式を使う。
規約：単位成分の可逆性としての局所性。使われ方：本質的な像の同定。 -/
lemma isLocal_inclusion (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌) :
    r.IsLocal y.val := by
  let i := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι
  let η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (i ≫ 𝟙 X) (i ≫ r.localization) :=
    (hoFunctor.map ((pre i).app X)).toFunctor.map r.unit
  haveI : IsIso η := r.adjunction.unit_precompRight_isIso
  have h : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η y) := inferInstance
  have he := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_precomp r.unit i y
  change IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate r.unit (i.app (Opposite.op ⦋0⦌) y))
  exact he ▸ h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory (isLocal_inclusion)


/-- 概要：局所対象の条件は hX の同型で不変。
方針：単位の自然性の可換式で三つの可逆因子から残りを可逆にする。
規約：P の同型不変性を使わない。使われ方：反射の本質的な像の閉性。 -/
lemma isLocal_of_vertexIso {x y : X _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) (hx : r.IsLocal x) :
    r.IsLocal y := by
  haveI : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit x) := hx
  have h := functorHomEvaluate_naturality r.unit e.hom
  have hid : (hoFunctor.map (𝟙 X)).toFunctor = 𝟭 (hoFunctor.obj X) := by
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hm : (hoFunctor.map (𝟙 X)).toFunctor.map e.hom = e.hom := by
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, Cat.Hom.id_map,
      CategoryTheory.Functor.id_map] using
      CategoryTheory.Functor.congr_hom hid e.hom
  rw [hm] at h
  have ht : e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit x ≫ (hoFunctor.map r.localization).toFunctor.map e.hom := by
    exact h
  exact IsIso.of_isIso_fac_left ht

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory (isLocal_of_vertexIso)


/-- 概要：局所対象は元の全部分圏の像と同型な対象でちょうど与えられる。
方針：局所単位の逆で反射像からの同型を作り、逆方向は像の局所性と同型不変性を使う。
規約：頂点の等号や P への所属には強めない。
使われ方：反射の局所対象の本質的な像による特徴づけ。 -/
@[kerodon 06TB]
lemma isLocal_iff_essentialImage (x : X _⦋0⦌) :
    r.IsLocal x ↔ ∃ y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso y.val x) := by
  constructor
  · intro hx
    haveI : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit x) := hx
    exact ⟨r.reflector.app (Opposite.op ⦋0⦌) x, ⟨(asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit x)).symm⟩⟩
  · rintro ⟨y, ⟨e⟩⟩
    exact r.isLocal_of_vertexIso e (r.isLocal_inclusion y)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory (isLocal_iff_essentialImage)


/-- 概要：反射の値は局所対象。
方針：reflector の値を部分圏の頂点と見て像の局所性を使う。
規約：元の P への所属に加えた本質的な局所性。使われ方：反射の局所対象への制限。 -/
lemma isLocal_localization (x : X _⦋0⦌) :
    r.IsLocal (r.localization.app (Opposite.op ⦋0⦌) x) :=
  r.isLocal_inclusion (r.reflector.app (Opposite.op ⦋0⦌) x)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory (isLocal_localization)


/-- 概要：局所対象の張る充満部分 ∞ 圏。
方針：単位が可逆な頂点を全て取り出す。
規約：元の P の同型閉包に相当する対象集合。
使われ方：反射的局所化の局所対象の圏。 -/
def localSubcomplex : X.Subcomplex := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X r.IsLocal

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory (localSubcomplex)


/-- 概要：局所対象の全部分複体は quasicategory。
方針：頂点条件の全部分複体の一般性質。
規約：P の同型不変性は不要。使われ方：局所対象への反射像の制限。 -/
instance localSubcomplex_quasicategory : Quasicategory (r.localSubcomplex : SSet.{u}) :=
  inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X r.IsLocal : SSet.{u}))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory (localSubcomplex_quasicategory)


/-- 概要：反射自己関手は局所対象の全部分圏に値を取る。
方針：全頂点で反射像が局所であることを使い持ち上げる。
規約：包含後の射は元の localization と厳密に一致する。
使われ方：局所対象を標的とした反射の表示。 -/
def localizationToLocalSubcomplex : X ⟶ (r.localSubcomplex : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift r.IsLocal r.localization r.isLocal_localization

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory (localizationToLocalSubcomplex)


/-- 概要：局所対象への持ち上げを含めると元の反射自己関手。
方針：全部分複体への持ち上げの包含公式。
規約：厳密な等式。使われ方：反射の型の変更との整合。 -/
lemma localizationToLocalSubcomplex_ι :
    r.localizationToLocalSubcomplex ≫ r.localSubcomplex.ι = r.localization :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory (localizationToLocalSubcomplex_ι)


end ReflectiveSubcategory
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
