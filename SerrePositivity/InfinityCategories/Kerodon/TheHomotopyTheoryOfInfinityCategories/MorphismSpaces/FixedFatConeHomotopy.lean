module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinTimeInput

/-!
概要：両端固定の fat join 図式のホモトピーを固定頂点の錐の族のホモトピーへ戻す。
方針：時間を左因子へ移した円柱を両端と貼り、固定頂点の curry を使う。
規約：ホモトピーの全時間で頂点と元の図式を厳密に固定する。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の比較のホモトピー右逆の構成。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：両端固定の図式のホモトピーを時間付き左因子の fat join 図式にする。
方針：円柱で時間を交換し、定値の左端と元の右図式で貼り合わせる。
規約：ホモトピーの逆向きや充填性は要求しない。
使われ方：Kerodon §4.6.6（Tag 04HY） の図式のホモトピーから族のホモトピーへの構成。 -/
noncomputable def fixedFatConeTimeDiagram {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ⟶ X} (H : SSet.Homotopy F G)
    (hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ SSet.const x)
    (hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (A ⊗ (Δ[1] : SSet.{u})) K ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinDesc (SSet.const x) p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTimeInput A K ≫ H.h)
    (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTimeInput_zero, Category.assoc, hx,
      SSet.comp_const, SSet.comp_const])
    (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTimeInput_one, Category.assoc, hp,
      ← Category.assoc, lift_fst])

/-- 概要：時間付き fat join 図式の左端は元の頂点に定値。
方針：貼り合わせの左端の式を使う。
規約：全ての時間を含む射の等式。
使われ方：Kerodon §4.6.6（Tag 04HY） の固定頂点の curry の条件。 -/
lemma fixedFatConeTimeDiagram_inl {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ⟶ X} (H : SSet.Homotopy F G)
    (hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ SSet.const x)
    (hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (A ⊗ (Δ[1] : SSet.{u})) K ≫ fixedFatConeTimeDiagram H hx hp = SSet.const x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_desc _ _ _ _ _

/-- 概要：時間付き fat join 図式の右端は元の図式に一致する。
方針：貼り合わせの右端の式を使う。
規約：ホモトピーの全時間で図式を固定する。
使われ方：Kerodon §4.6.6（Tag 04HY） の固定頂点の curry の条件。 -/
lemma fixedFatConeTimeDiagram_inr {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ⟶ X} (H : SSet.Homotopy F G)
    (hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ SSet.const x)
    (hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (A ⊗ (Δ[1] : SSet.{u})) K ≫ fixedFatConeTimeDiagram H hx hp = p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_desc _ _ _ _ _

/-- 概要：時間付き図式の零時間への制限は始点の錐の展開。
方針：円柱と左右の因子で比較し、円柱ではホモトピーの始点の式を使う。
規約：始点と終点は実際の固定頂点の錐の族で与える。
使われ方：Kerodon §4.6.6（Tag 04HY） の移送した族のホモトピーの始点。 -/
lemma fixedFatConeTimeDiagram_zero {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x)
    (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry g))
    (hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ SSet.const x)
    (hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap (SSet.ι₀ (X := A)) (𝟙 K) ≫ fixedFatConeTimeDiagram H hx hp =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_hom_ext
  · rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A K), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_map, Category.assoc,
      fixedFatConeTimeDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_desc,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap (SSet.ι₀ (X := A)) (𝟙 K)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTimeInput_time_zero, Category.assoc, H.h₀]
  · rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_map, Category.assoc,
      fixedFatConeTimeDiagram_inl, SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry_inl]
  · rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_map, Category.id_comp,
      fixedFatConeTimeDiagram_inr, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry_inr]

/-- 概要：時間付き図式の一時間への制限は終点の錐の展開。
方針：円柱と左右の因子で比較し、円柱ではホモトピーの終点の式を使う。
規約：始点と終点は実際の固定頂点の錐の族で与える。
使われ方：Kerodon §4.6.6（Tag 04HY） の移送した族のホモトピーの終点。 -/
lemma fixedFatConeTimeDiagram_one {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x)
    (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry g))
    (hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ SSet.const x)
    (hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap (SSet.ι₁ (X := A)) (𝟙 K) ≫ fixedFatConeTimeDiagram H hx hp =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_hom_ext
  · rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A K), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_map, Category.assoc,
      fixedFatConeTimeDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_desc,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap (SSet.ι₁ (X := A)) (𝟙 K)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTimeInput_time_one, Category.assoc, H.h₁]
  · rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_map, Category.assoc,
      fixedFatConeTimeDiagram_inl, SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry_inl]
  · rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_map, Category.id_comp,
      fixedFatConeTimeDiagram_inr, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry_inr]

/-- 概要：両端を固定する図式のホモトピーは固定頂点の錐の族のホモトピーを与える。
方針：時間付き図式を固定頂点で curry し、展開の単射性で端点を計算する。
規約：充填性を要求しない構成である。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS） の比較のホモトピー右逆。 -/
noncomputable def fixedFatConeHomotopyOfDiagram {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x)
    (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry g))
    (hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ SSet.const x)
    (hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p) :
    SSet.Homotopy f g where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeCurry (fixedFatConeTimeDiagram H hx hp)
    (fixedFatConeTimeDiagram_inl H hx hp) (fixedFatConeTimeDiagram_inr H hx hp)
  h₀ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry_injective p x
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry_curry]
    exact fixedFatConeTimeDiagram_zero f g H hx hp
  h₁ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry_injective p x
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeUncurry_curry]
    exact fixedFatConeTimeDiagram_one f g H hx hp
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
