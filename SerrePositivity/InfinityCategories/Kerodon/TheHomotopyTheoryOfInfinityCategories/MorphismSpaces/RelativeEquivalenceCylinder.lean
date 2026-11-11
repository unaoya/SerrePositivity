module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCylinder
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionPushoutProduct

/-!
概要：部分を固定した可逆な円柱。
方針：A→B に対し A×E を A に潰し、端点を pushout-product の pushout として比較する。
規約：端点の同値性は単射 A→B の場合に証明する。
使われ方：Kerodon §4.6.2（Tag 01HM） のセルの貼り合わせ。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：可逆な円柱の端点は元の単体集合の射に自然。
方針：直積の二つの成分を計算する。
規約：Bool の両端点に適用する。
使われ方：Kerodon §4.6.2（Tag 01HM） の部分を固定した円柱。 -/
lemma equivalenceCylinderEndpoint_naturality {A B : SSet.{u}} (i : A ⟶ B) (b : Bool) :
    i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint B b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A b ≫ (i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 概要：A の部分で時間変化を潰した B の可逆な円柱。
方針：A×E→B×E と A への射影の pushout を取る。
規約：定義には i の単射性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の相対的な貼り合わせ。 -/
noncomputable def relativeEquivalenceCylinder {A B : SSet.{u}} (i : A ⟶ B) : SSet.{u} :=
  pushout (i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) (fst A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval)

/-- 概要：部分を固定した可逆な円柱への端点の包含。
方針：直積円柱の端点と pushout 包含を合成する。
規約：二つの端点の A への制限は一致する。
使われ方：Kerodon §4.6.2（Tag 01HM） の相対写像円柱。 -/
noncomputable def relativeEquivalenceCylinderEndpoint {A B : SSet.{u}} (i : A ⟶ B) (b : Bool) :
    B ⟶ relativeEquivalenceCylinder i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint B b ≫ pushout.inl _ _

/-- 概要：相対円柱の二つの端点は固定する部分で一致する。
方針：端点の自然性と pushout の可換性を使う。
規約：右辺は A の pushout 包含。
使われ方：Kerodon §4.6.2（Tag 01HM） の相対的なホモトピー。 -/
lemma relativeEquivalenceCylinderEndpoint_fixed {A B : SSet.{u}} (i : A ⟶ B) (b : Bool) :
    i ≫ relativeEquivalenceCylinderEndpoint i b =
      pushout.inr (i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) (fst A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) := by
  unfold relativeEquivalenceCylinderEndpoint
  rw [← Category.assoc, equivalenceCylinderEndpoint_naturality, Category.assoc,
    pushout.condition, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint_fst, Category.id_comp]

/-- 概要：端点の pushout-product の角から B への射。
方針：B×単位を B、A×E を A→B で写して貼り合わせる。
規約：可逆な区間の指定端点を使う。
使われ方：Kerodon §4.6.2（Tag 01HM） の相対円柱の端点の検出。 -/
noncomputable def relativeEquivalenceCylinderCorner {A B : SSet.{u}} (i : A ⟶ B) (b : Bool) :
    (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
      i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint b)).pt ⟶ B :=
  (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
    i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint b)).isPushout.desc (ρ_ B).hom
      (fst A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ≫ i) (by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro s
        rfl)

/-- 概要：相対円柱の端点は pushout-product の pushout で得られる。
方針：両方の pushout の普遍性を比較する。
規約：定義段階では i の単射性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の端点の単射性と同値性。 -/
lemma relativeEquivalenceCylinderEndpoint_isPushout {A B : SSet.{u}} (i : A ⟶ B) (b : Bool) :
    IsPushout (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
      i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint b)).ι (relativeEquivalenceCylinderCorner i b)
      (pushout.inl (i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) (fst A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval))
      (relativeEquivalenceCylinderEndpoint i b) := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
    i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint b)
  have hl : sq.inl ≫ relativeEquivalenceCylinderCorner i b = (ρ_ B).hom :=
    sq.isPushout.inl_desc _ _ _
  have hr : sq.inr ≫ relativeEquivalenceCylinderCorner i b =
      fst A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ≫ i := sq.isPushout.inr_desc _ _ _
  refine IsPushout.mk' ?_ ?_ ?_
  · apply sq.hom_ext
    · rw [← Category.assoc, sq.inl_ι, ← Category.assoc, hl]
      unfold relativeEquivalenceCylinderEndpoint _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rfl
    · rw [← Category.assoc, sq.inr_ι, ← Category.assoc, hr, Category.assoc,
        relativeEquivalenceCylinderEndpoint_fixed]
      exact pushout.condition
  · intro T φ ψ h₀ h₁
    apply pushout.hom_ext h₀
    have he := congrArg (fun k ↦ i ≫ k) h₁
    simpa only [← Category.assoc, relativeEquivalenceCylinderEndpoint_fixed] using he
  · intro T a c hac
    change sq.ι ≫ a = relativeEquivalenceCylinderCorner i b ≫ c at hac
    have hw : (i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) ≫ a =
        fst A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ≫ (i ≫ c) := by
      have he := congrArg (fun k ↦ sq.inr ≫ k) hac
      rw [← Category.assoc, sq.inr_ι, ← Category.assoc, hr, Category.assoc] at he
      exact he
    let F := pushout.desc a (i ≫ c) hw
    refine ⟨F, pushout.inl_desc _ _ _, ?_⟩
    have he := congrArg (fun k ↦ sq.inl ≫ k) hac
    have he' : (B ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint b) ≫ a = (ρ_ B).hom ≫ c := by
      rw [← Category.assoc, sq.inl_ι, ← Category.assoc, hl] at he
      exact he
    unfold relativeEquivalenceCylinderEndpoint
    rw [Category.assoc, pushout.inl_desc]
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint
    rw [Category.assoc, he', Iso.inv_hom_id_assoc]

/-- 概要：単射で固定された相対円柱の端点は単射。
方針：単射の pushout-product の単射性を pushout で移す。
規約：i の単射性を要求する。
使われ方：Kerodon §4.6.2（Tag 01HM） の相対的な因子分解。 -/
instance relativeEquivalenceCylinderEndpoint_mono {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (b : Bool) : Mono (relativeEquivalenceCylinderEndpoint i b) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.mono_pushoutObjObj_ι i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint b)
    (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint b))
  exact Adhesive.mono_of_isPushout_of_mono_left
    (relativeEquivalenceCylinderEndpoint_isPushout i b)

/-- 概要：単射で固定された相対円柱の端点は前合成の同値条件を満たす。
方針：端点の同値条件を pushout-product と pushout により移す。
規約：i の単射性を要求する。
使われ方：Kerodon §4.6.2（Tag 01HM） のセルの貼り合わせ。 -/
lemma isPrecompositionEquivalence_relativeEquivalenceCylinderEndpoint {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (b : Bool) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (relativeEquivalenceCylinderEndpoint i b) := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
    i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint b)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.mono_pushoutObjObj_ι i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint b) sq
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_equivalenceIntervalPoint b).pushoutObjObj_right i sq
  exact hp.of_isPushout (relativeEquivalenceCylinderEndpoint_isPushout i b)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
