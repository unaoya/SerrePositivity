module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RelativeEquivalenceCylinder
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RelativeCylinderDisjoint

/-!
概要：固定部分を持つ射の可逆な写像円柱。
方針：相対円柱の一端を貼り合わせ、残った端点の単射性を各次数の分離関数で示す。
規約：固定部分の像の単射性を明記する。
使われ方：Kerodon §4.6.2（Tag 01HM） の同値な図式の貼り合わせ。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：相対的な可逆円柱から元の単体集合への射影。
方針：円柱の第一射影と固定部分の包含を貼り合わせる。
規約：定義には単射性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の相対写像円柱の収縮。 -/
noncomputable def relativeEquivalenceCylinderProjection {A B : SSet.{u}} (i : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinder i ⟶ B :=
  pushout.desc (fst B _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) i (by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    rfl)

/-- 概要：相対円柱の両端を射影すると恒等射になる。
方針：pushout の制限の計算と端点の射影の計算を使う。
規約：固定部分を含む厳密な等式。
使われ方：Kerodon §4.6.2（Tag 01HM） の円柱の収縮。 -/
lemma relativeEquivalenceCylinderEndpoint_projection {A B : SSet.{u}} (i : A ⟶ B) (b : Bool) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint i b ≫ relativeEquivalenceCylinderProjection i = 𝟙 B := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint relativeEquivalenceCylinderProjection
  rw [Category.assoc, pushout.inl_desc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint_fst]

/-- 概要：固定部分を持つ射の可逆な写像円柱。
方針：相対円柱の零端を f で貼り合わせる。
規約：i は固定部分 A→B、f は B→C。
使われ方：Kerodon §4.6.2（Tag 01HM） の相対的な因子分解。 -/
noncomputable def relativeEquivalenceMappingCylinder {A B C : SSet.{u}}
    (i : A ⟶ B) (f : B ⟶ C) : SSet.{u} :=
  pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint i false) f

/-- 概要：相対写像円柱への始域の残った端点の包含。
方針：相対円柱の一端を写像円柱へ写す。
規約：固定部分の両端は既に一致している。
使われ方：Kerodon §4.6.2（Tag 01HM） の相対的な因子分解。 -/
noncomputable def relativeEquivalenceMappingCylinderIn {A B C : SSet.{u}}
    (i : A ⟶ B) (f : B ⟶ C) : B ⟶ relativeEquivalenceMappingCylinder i f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint i true ≫ pushout.inl _ _

/-- 概要：相対写像円柱の残った端点は固定部分の像が単射なら単射。
方針：二段の pushout を各次数で評価し、分離関数の補題を適用する。
規約：i と i≫f の単射性を仮定する。f 自身の単射性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の相対的な因子分解。 -/
instance relativeEquivalenceMappingCylinderIn_mono {A B C : SSet.{u}}
    (i : A ⟶ B) (f : B ⟶ C) [Mono i] [Mono (i ≫ f)] :
    Mono (relativeEquivalenceMappingCylinderIn i f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  apply (mono_iff_injective _).2
  let e₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint.{u} false).app n PUnit.unit
  let e₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint.{u} true).app n PUnit.unit
  have he : e₁ ≠ e₀ := by
    intro h
    have hh := congrArg (fun q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval.{u}.obj n ↦ ((q.obj 0).as).down) h
    change true = false at hh
    cases hh
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeCylinder_endpoint_injective (i.app n) (f.app n)
    ((pushout.inl (i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) (fst A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval)).app n)
    ((pushout.inr (i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) (fst A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval)).app n)
    ((pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint i false) f).app n)
    ((pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint i false) f).app n) e₀ e₁ he
    ((IsPushout.of_hasPushout (i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) (fst A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval)).map
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n))
    ((IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint i false) f).map
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n))
    ((mono_iff_injective ((i ≫ f).app n)).mp inferInstance)

/-- 概要：相対写像円柱の始域の包含は固定部分で終域の包含に一致する。
方針：相対円柱の二端点の一致と写像円柱の pushout の可換性を使う。
規約：単射性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の under 圏での因子分解。 -/
lemma relativeEquivalenceMappingCylinderIn_fixed {A B C : SSet.{u}}
    (i : A ⟶ B) (f : B ⟶ C) :
    i ≫ relativeEquivalenceMappingCylinderIn i f =
      (i ≫ f) ≫ pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint i false) f := by
  have he := congrArg (fun k ↦ i ≫ k)
    (pushout.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint i false) (g := f))
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint_fixed, ← Category.assoc] at he
  unfold relativeEquivalenceMappingCylinderIn
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint_fixed]
  exact he

/-- 概要：相対写像円柱から終域への収縮。
方針：相対円柱の射影後に f を適用し、終域上で恒等として貼り合わせる。
規約：定義には単射性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の相対写像円柱。 -/
noncomputable def relativeEquivalenceMappingCylinderOut {A B C : SSet.{u}}
    (i : A ⟶ B) (f : B ⟶ C) : relativeEquivalenceMappingCylinder i f ⟶ C :=
  pushout.desc (relativeEquivalenceCylinderProjection i ≫ f) (𝟙 C) (by
    rw [← Category.assoc, relativeEquivalenceCylinderEndpoint_projection,
      Category.id_comp, Category.comp_id])

/-- 概要：相対写像円柱を経由する合成は元の射になる。
方針：貼り合わせの相対円柱上の計算を使う。
規約：固定部分を保つ厳密な等式。
使われ方：Kerodon §4.6.2（Tag 01HM） の射の因子分解。 -/
lemma relativeEquivalenceMappingCylinderIn_out {A B C : SSet.{u}}
    (i : A ⟶ B) (f : B ⟶ C) :
    relativeEquivalenceMappingCylinderIn i f ≫ relativeEquivalenceMappingCylinderOut i f = f := by
  unfold relativeEquivalenceMappingCylinderIn relativeEquivalenceMappingCylinderOut
  rw [Category.assoc, pushout.inl_desc, ← Category.assoc,
    relativeEquivalenceCylinderEndpoint_projection, Category.id_comp]

/-- 概要：固定部分が単射の相対写像円柱の収縮は前合成の同値条件を満たす。
方針：終域の包含を相対円柱の端点の pushout として検出し、収縮に二対三則を使う。
規約：f 自身の同値条件は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の相対的な因子分解。 -/
lemma isPrecompositionEquivalence_relativeEquivalenceMappingCylinderOut {A B C : SSet.{u}}
    (i : A ⟶ B) [Mono i] (f : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (relativeEquivalenceMappingCylinderOut i f) := by
  have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_relativeEquivalenceCylinderEndpoint i false).of_isPushout
    (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint i false) f)
  apply hs.cancel_left
  have he : pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint i false) f ≫
      relativeEquivalenceMappingCylinderOut i f = 𝟙 C := pushout.inr_desc _ _ _
  rw [he]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id _

/-- 概要：固定部分が単射の射の同値条件は相対写像円柱の始域の包含で検出される。
方針：収縮の同値条件と厳密な因子分解に二対三則を使う。
規約：この同値には i≫f の単射性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の同値な図式の貼り合わせ。 -/
lemma isPrecompositionEquivalence_iff_relativeEquivalenceMappingCylinderIn {A B C : SSet.{u}}
    (i : A ⟶ B) [Mono i] (f : B ⟶ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (relativeEquivalenceMappingCylinderIn i f) := by
  have hr := isPrecompositionEquivalence_relativeEquivalenceMappingCylinderOut i f
  constructor
  · intro hf
    apply hr.cancel_right
    rwa [relativeEquivalenceMappingCylinderIn_out]
  · intro hi
    have h := hi.comp hr
    rwa [relativeEquivalenceMappingCylinderIn_out] at h

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
