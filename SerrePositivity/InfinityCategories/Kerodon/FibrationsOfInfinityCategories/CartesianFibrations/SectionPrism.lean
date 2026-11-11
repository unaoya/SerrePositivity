module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialFixedContraction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.MappingCylinderOverMono
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
概要：section の始域を収縮させ、パラメータを固定する prism と頂点の部分複体。
方針：時間と始域への射影で収縮し、パラメータへの射影を保持する。
規約：頂点の部分複体は各次数でその頂点の定値単体だけを持つ。
使われ方：評価と境界を固定した cocartesian section の延長。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：一つの頂点の定値単体からなる部分複体。
方針：各次数で定値単体の singleton を取る。
規約：辺を持つ全部分複体とは異なり、退化単体だけを持つ。
使われ方：評価を固定する部分の積の和への包含。 -/
def sectionVertexSpan {A : SSet.{u}} (v : A _⦋0⦌) : A.Subcomplex where
  obj n := {_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v n.unop.len}
  map {n m} α s hs := by
    change s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v n.unop.len at hs
    change A.map α (s) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v m.unop.len
    rw [hs]
    simpa only [Quiver.Hom.op_unop] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback v α.unop

/-- 概要：頂点の部分複体の包含は定値射。
方針：各単体の singleton への所属を使う。
規約：充填性の仮定はない。
使われ方：収縮が評価を固定する条件の適用。 -/
lemma sectionVertexSpan_ι {A : SSet.{u}} (v : A _⦋0⦌) :
    (sectionVertexSpan v).ι = SSet.const v := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  exact x.property

/-- 概要：指定頂点での評価を積の頂点部分へ持ち上げる。
方針：定値単体の所属の証明を添え、パラメータは保持する。
規約：第一因子が頂点の部分複体。
使われ方：頂点部分上の等式から厳密な評価条件を回収する。 -/
def sectionVertexParameter {A T : SSet.{u}} (v : A _⦋0⦌) :
    T ⟶ (sectionVertexSpan v : SSet.{u}) ⊗ T :=
  lift ((sectionVertexSpan v).lift (SSet.const v) (by
    rintro n x ⟨y, rfl⟩
    rfl)) (𝟙 T)

/-- 概要：頂点部分への持ち上げの包含は通常の頂点評価の包含。
方針：直積の成分を計算する。
規約：パラメータの全次数で成立する。
使われ方：指定した評価での一致。 -/
lemma sectionVertexParameter_ι {A T : SSet.{u}} (v : A _⦋0⦌) :
    sectionVertexParameter (T := T) v ≫ ((sectionVertexSpan v).ι ▷ T) =
      lift (SSet.const v) (𝟙 T) := rfl

/-- 概要：始域の prism を、パラメータを動かさない積上の prism へ延長する。
方針：収縮への二つの射影と保持したパラメータを直積へ束ねる。
規約：C は任意のホモトピー。
使われ方：境界上の既存 section を始対象の収縮に沿って読む。 -/
def sectionPrism {A : SSet.{u}} (C : (Δ[1] : SSet.{u}) ⊗ A ⟶ A) (T : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (A ⊗ T) ⟶ A ⊗ T :=
  lift ((Δ[1] ◁ fst A T) ≫ C) (snd Δ[1] (A ⊗ T) ≫ snd A T)

/-- 概要：積上の prism はパラメータの制限と可換。
方針：二つの直積成分を計算する。
規約：制限射の単射性は不要。
使われ方：境界の輸送と全体の基底の整合性。 -/
lemma sectionPrism_naturality {A U T : SSet.{u}}
    (C : (Δ[1] : SSet.{u}) ⊗ A ⟶ A) (j : U ⟶ T) :
    (Δ[1] ◁ (A ◁ j)) ≫ sectionPrism C T = sectionPrism C U ≫ (A ◁ j) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [sectionPrism, Category.assoc, lift_fst, whiskerLeft_fst]
    rw [← Category.assoc, ← whiskerLeft_comp, whiskerLeft_fst]
  · simp only [sectionPrism, Category.assoc, lift_snd, whiskerLeft_snd]
    rfl

/-- 概要：積上の prism の端点は、元の prism の端点と恒等パラメータの積。
方針：二つの直積成分で端点の自然性を使う。
規約：時刻は両端点のいずれもよい。
使われ方：輸送の始点と終点の計算。 -/
lemma sectionPrism_endpoint {A T : SSet.{u}}
    (C : (Δ[1] : SSet.{u}) ⊗ A ⟶ A) (k : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint k (A ⊗ T) ≫ sectionPrism C T =
      lift (fst A T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint k A ≫ C) (snd A T) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [sectionPrism, Category.assoc, lift_fst]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc]
  · simp only [sectionPrism, Category.assoc, lift_snd]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_snd, Category.id_comp]

/-- 概要：定値写像から始まる prism の積も指定頂点での評価から始まる。
方針：端点の式と定値射への合成を計算する。
規約：パラメータを保持する。
使われ方：境界の輸送の始点の一致。 -/
lemma sectionPrism_zero {A T : SSet.{u}} (v : A _⦋0⦌)
    (C : (Δ[1] : SSet.{u}) ⊗ A ⟶ A) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ C = SSet.const v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (A ⊗ T) ≫ sectionPrism C T =
      snd A T ≫ lift (SSet.const v) (𝟙 T) := by
  rw [sectionPrism_endpoint, hC, SSet.comp_const]
  rfl

/-- 概要：恒等写像で終わる prism の積も恒等写像で終わる。
方針：端点の式で二つの射影を組み合わせる。
規約：射の厳密な等式。
使われ方：延長した section の境界の回収。 -/
lemma sectionPrism_one {A T : SSet.{u}}
    (C : (Δ[1] : SSet.{u}) ⊗ A ⟶ A) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ C = 𝟙 A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (A ⊗ T) ≫ sectionPrism C T = 𝟙 _ := by
  rw [sectionPrism_endpoint, hC, Category.comp_id, lift_fst_snd]

/-- 概要：頂点を固定する prism は頂点部分とパラメータの積全体で定値の輸送。
方針：頂点部分の包含を定値射と読み、固定条件を第一成分に適用する。
規約：固定条件は任意のパラメータ上で仮定する。
使われ方：境界上の輸送と評価上の定値輸送の一致。 -/
lemma sectionPrism_vertex {A T : SSet.{u}} (v : A _⦋0⦌)
    (C : (Δ[1] : SSet.{u}) ⊗ A ⟶ A)
    (hC : ∀ K : SSet.{u}, (Δ[1] ◁ (SSet.const v : K ⟶ A)) ≫ C = SSet.const v) :
    (Δ[1] ◁ ((sectionVertexSpan v).ι ▷ T)) ≫ sectionPrism C T =
      snd Δ[1] _ ≫ ((sectionVertexSpan v).ι ▷ T) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [sectionPrism, Category.assoc, lift_fst, whiskerRight_fst]
    rw [← Category.assoc, ← whiskerLeft_comp, whiskerRight_fst, sectionVertexSpan_ι,
      SSet.comp_const, hC, SSet.comp_const]
  · simp only [sectionPrism, Category.assoc, lift_snd, whiskerRight_snd]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
