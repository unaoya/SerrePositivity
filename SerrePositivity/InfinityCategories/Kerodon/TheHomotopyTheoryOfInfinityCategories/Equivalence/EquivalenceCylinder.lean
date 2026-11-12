module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CodiscreteNerve
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutDisjoint

/-!
概要：可逆な区間による単体集合の射の写像円柱。
方針：二対象の codiscrete 圏の nerve の片端で貼り合わせる。
規約：quasicategory の交換やモデル構造を定義しない。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較射の貼り合わせ。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：二つの対象と一意な可逆射を持つ圏の nerve の区間。
方針：codiscrete 圏の nerve を用いる。
規約：ULift によって任意の宇宙の単体集合にする。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.6.2（Tag 01HM） の可逆な区間。 -/
def equivalenceInterval : SSet.{u} := nerve (Codiscrete (ULift.{u} Bool))

/-- 概要：可逆な区間の指定された端点。
方針：Bool に対応する対象の頂点への定値射を取る。
規約：false と true は異なる端点。
使われ方：Kerodon §4.6.2（Tag 01HM） の写像円柱。 -/
def equivalenceIntervalPoint (b : Bool) : 𝟙_ SSet.{u} ⟶ equivalenceInterval :=
  SSet.const (nerveEquiv.symm (Codiscrete.mk (ULift.up b)))

/-- 概要：可逆な区間の端点は単射。
方針：標準零単体の各次数の単体が一意であることを使う。
規約：両方の端点に適用する。
使われ方：Kerodon §4.6.2（Tag 01HM） の単射による貼り合わせ。 -/
instance equivalenceIntervalPoint_mono (b : Bool) : Mono (equivalenceIntervalPoint.{u} b) := by
  exact isTerminalTensorUnit.mono_from _

/-- 概要：可逆な区間の端点は前合成の同値条件を満たす。
方針：codiscrete 圏の nerve の全境界充填を使う。
規約：標準区間 Δ[1] の端点の同値性は主張しない。
使われ方：Kerodon §4.6.2（Tag 01HM） の可逆な写像円柱。 -/
lemma isPrecompositionEquivalence_equivalenceIntervalPoint (b : Bool) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (equivalenceIntervalPoint.{u} b) := by
  let e : (Δ[0] : SSet.{u}) ≅ 𝟙_ SSet.{u} :=
    stdSimplex.isTerminalObj₀.uniqueUpToIso isTerminalTensorUnit
  let q : (Δ[0] : SSet.{u}) ⟶ equivalenceInterval :=
    SSet.const (nerveEquiv.symm (Codiscrete.mk (ULift.up b)))
  have he : equivalenceIntervalPoint b = e.inv ≫ q := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [he]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e.symm).comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isContractibleKan_codiscreteNerve (ULift.{u} Bool)).isPrecompositionEquivalence_point q)

/-- 概要：単体集合と可逆な区間の直積への端点の包含。
方針：右単位子の逆と区間の端点の直積を合成する。
規約：第一成分は恒等。
使われ方：Kerodon §4.6.2（Tag 01HM） の写像円柱。 -/
def equivalenceCylinderEndpoint (A : SSet.{u}) (b : Bool) :
    A ⟶ A ⊗ equivalenceInterval :=
  (ρ_ A).inv ≫ A ◁ equivalenceIntervalPoint b

/-- 概要：可逆な円柱の端点は単射。
方針：端点の単射性を直積と単位子の同型で移す。
規約：任意の単体集合 A。
使われ方：Kerodon §4.6.2（Tag 01HM） の写像円柱の貼り合わせ。 -/
instance equivalenceCylinderEndpoint_mono (A : SSet.{u}) (b : Bool) :
    Mono (equivalenceCylinderEndpoint A b) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  apply (mono_iff_injective _).2
  intro a a' h
  exact congrArg Prod.fst h

/-- 概要：可逆な円柱の端点は前合成の同値条件を満たす。
方針：端点の同値条件の直積による保存を使う。
規約：A の quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の写像円柱の同値性。 -/
lemma isPrecompositionEquivalence_equivalenceCylinderEndpoint (A : SSet.{u}) (b : Bool) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (equivalenceCylinderEndpoint A b) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (ρ_ A).symm).comp
    ((isPrecompositionEquivalence_equivalenceIntervalPoint b).whiskerLeft A)

/-- 概要：可逆な円柱の端点を射影すると恒等射になる。
方針：直積の第一成分を計算する。
規約：両方の端点に適用する。
使われ方：Kerodon §4.6.2（Tag 01HM） の写像円柱の収縮。 -/
lemma equivalenceCylinderEndpoint_fst (A : SSet.{u}) (b : Bool) :
    equivalenceCylinderEndpoint A b ≫ fst A equivalenceInterval = 𝟙 A := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 概要：単体集合の射の可逆な写像円柱。
方針：可逆な円柱の零端を指定された射で貼り合わせる。
規約：写像円柱自身の quasicategory 性は要求しない。
使われ方：Kerodon §4.6.2（Tag 01HM） の同値比較の貼り合わせ。 -/
noncomputable def equivalenceMappingCylinder {A B : SSet.{u}} (f : A ⟶ B) : SSet.{u} :=
  pushout (equivalenceCylinderEndpoint A false) f

/-- 概要：写像円柱への元の始域の包含。
方針：貼り合わせていない一端を包含する。
規約：false 端を貼り合わせ、true 端を残す。
使われ方：Kerodon §4.6.2（Tag 01HM） の射の因子分解。 -/
noncomputable def equivalenceMappingCylinderIn {A B : SSet.{u}} (f : A ⟶ B) :
    A ⟶ equivalenceMappingCylinder f :=
  equivalenceCylinderEndpoint A true ≫ pushout.inl _ _

/-- 概要：写像円柱への始域の包含は単射。
方針：二つの区間端点が各次数で交わらないことを使う。
規約：元の射 f の単射性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の単射への因子分解。 -/
instance equivalenceMappingCylinderIn_mono {A B : SSet.{u}} (f : A ⟶ B) :
    Mono (equivalenceMappingCylinderIn f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mono_pushout_inl_comp_of_disjoint (IsPushout.of_hasPushout _ _)
  intro n a t h
  have he := congrArg (fun s : (A ⊗ equivalenceInterval.{u}).obj n ↦
    ((s.2.obj 0).as).down) h
  change false = true at he
  cases he

/-- 概要：写像円柱から元の終域への収縮。
方針：円柱上は射影後に f、終域上は恒等射として貼り合わせる。
規約：元の f への厳密な因子分解を与える。
使われ方：Kerodon §4.6.2（Tag 01HM） の写像円柱の同値性。 -/
noncomputable def equivalenceMappingCylinderOut {A B : SSet.{u}} (f : A ⟶ B) :
    equivalenceMappingCylinder f ⟶ B :=
  pushout.desc (fst A equivalenceInterval ≫ f) (𝟙 B) (by
    rw [← Category.assoc, equivalenceCylinderEndpoint_fst,
      Category.id_comp, Category.comp_id])

/-- 概要：写像円柱を経由する合成は元の射に一致する。
方針：pushout の円柱上の制限と一端の射影を計算する。
規約：厳密な等式。
使われ方：Kerodon §4.6.2（Tag 01HM） の射の因子分解。 -/
lemma equivalenceMappingCylinderIn_out {A B : SSet.{u}} (f : A ⟶ B) :
    equivalenceMappingCylinderIn f ≫ equivalenceMappingCylinderOut f = f := by
  unfold equivalenceMappingCylinderIn equivalenceMappingCylinderOut
  rw [Category.assoc, pushout.inl_desc, ← Category.assoc,
    equivalenceCylinderEndpoint_fst, Category.id_comp]

/-- 概要：写像円柱の収縮は前合成の同値条件を満たす。
方針：終域の包含を端点の pushout として同値にし、その収縮に二対三則を使う。
規約：元の射 f が同値であることは不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の射の因子分解。 -/
lemma isPrecompositionEquivalence_equivalenceMappingCylinderOut {A B : SSet.{u}}
    (f : A ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (equivalenceMappingCylinderOut f) := by
  have hi := (isPrecompositionEquivalence_equivalenceCylinderEndpoint A false).of_isPushout
    (IsPushout.of_hasPushout (equivalenceCylinderEndpoint A false) f)
  apply hi.cancel_left
  have he : pushout.inr (equivalenceCylinderEndpoint A false) f ≫
      equivalenceMappingCylinderOut f = 𝟙 B := pushout.inr_desc _ _ _
  rw [he]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id _

/-- 概要：元の射の前合成の同値条件は写像円柱の単射部分の条件と同値。
方針：収縮の同値条件と厳密な因子分解に二対三則を適用する。
規約：元の二つの単体集合の quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の同値な比較射の単射への還元。 -/
lemma isPrecompositionEquivalence_iff_equivalenceMappingCylinderIn {A B : SSet.{u}}
    (f : A ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (equivalenceMappingCylinderIn f) := by
  have hr := isPrecompositionEquivalence_equivalenceMappingCylinderOut f
  constructor
  · intro hf
    apply hr.cancel_right
    rwa [equivalenceMappingCylinderIn_out]
  · intro hi
    have h := hi.comp hr
    rwa [equivalenceMappingCylinderIn_out] at h

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
