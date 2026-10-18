module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FatJoinTimeInput

/-!
概要：両端固定の fat join 図式のホモトピーを固定頂点の錐の族のホモトピーへ戻す。
方針：時間を左因子へ移した円柱を両端と貼り、固定頂点の curry を使う。
規約：ホモトピーの全時間で頂点と元の図式を厳密に固定する。
使われ方：Kerodon §4.6.6、7.4.1.6、7.5.4.6 の比較のホモトピー右逆の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：両端固定の図式のホモトピーを時間付き左因子の fat join 図式にする。
方針：円柱で時間を交換し、定値の左端と元の右図式で貼り合わせる。
規約：ホモトピーの逆向きや充填性は要求しない。
使われ方：Kerodon §4.6.6 の図式のホモトピーから族のホモトピーへの構成。 -/
noncomputable def fixedFatConeTimeDiagram {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} {F G : fatJoin A K ⟶ X} (H : SSet.Homotopy F G)
    (hx : (fatJoinInl A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ SSet.const x)
    (hp : (fatJoinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p) :
    fatJoin (A ⊗ (Δ[1] : SSet.{u})) K ⟶ X :=
  fatJoinDesc (SSet.const x) p (fatJoinTimeInput A K ≫ H.h)
    (by rw [← Category.assoc, fatJoinTimeInput_zero, Category.assoc, hx,
      SSet.comp_const, SSet.comp_const])
    (by rw [← Category.assoc, fatJoinTimeInput_one, Category.assoc, hp,
      ← Category.assoc, lift_fst])

/-- 概要：時間付き fat join 図式の左端は元の頂点に定値。
方針：貼り合わせの左端の式を使う。
規約：全ての時間を含む射の等式。
使われ方：Kerodon §4.6.6 の固定頂点の curry の条件。 -/
lemma fixedFatConeTimeDiagram_inl {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} {F G : fatJoin A K ⟶ X} (H : SSet.Homotopy F G)
    (hx : (fatJoinInl A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ SSet.const x)
    (hp : (fatJoinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p) :
    fatJoinInl (A ⊗ (Δ[1] : SSet.{u})) K ≫ fixedFatConeTimeDiagram H hx hp = SSet.const x :=
  fatJoinInl_desc _ _ _ _ _

/-- 概要：時間付き fat join 図式の右端は元の図式に一致する。
方針：貼り合わせの右端の式を使う。
規約：ホモトピーの全時間で図式を固定する。
使われ方：Kerodon §4.6.6 の固定頂点の curry の条件。 -/
lemma fixedFatConeTimeDiagram_inr {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} {F G : fatJoin A K ⟶ X} (H : SSet.Homotopy F G)
    (hx : (fatJoinInl A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ SSet.const x)
    (hp : (fatJoinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p) :
    fatJoinInr (A ⊗ (Δ[1] : SSet.{u})) K ≫ fixedFatConeTimeDiagram H hx hp = p :=
  fatJoinInr_desc _ _ _ _ _

/-- 概要：時間付き図式の零時間への制限は始点の錐の展開。
方針：円柱と左右の因子で比較し、円柱ではホモトピーの始点の式を使う。
規約：始点と終点は実際の固定頂点の錐の族で与える。
使われ方：Kerodon §4.6.6 の移送した族のホモトピーの始点。 -/
lemma fixedFatConeTimeDiagram_zero {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} (f g : A ⟶ fixedEndpointFatConeSpace p x)
    (H : SSet.Homotopy (fixedFatConeUncurry f) (fixedFatConeUncurry g))
    (hx : (fatJoinInl A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ SSet.const x)
    (hp : (fatJoinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p) :
    fatJoinMap (SSet.ι₀ (X := A)) (𝟙 K) ≫ fixedFatConeTimeDiagram H hx hp =
      fixedFatConeUncurry f := by
  apply fatJoin_hom_ext
  · rw [← Category.assoc (fatJoinCylinder A K), fatJoinCylinder_map, Category.assoc,
      fixedFatConeTimeDiagram, fatJoinCylinder_desc,
      ← Category.assoc (fatJoinCylinderMap (SSet.ι₀ (X := A)) (𝟙 K)),
      fatJoinTimeInput_time_zero, Category.assoc, H.h₀]
  · rw [← Category.assoc (fatJoinInl A K), fatJoinInl_map, Category.assoc,
      fixedFatConeTimeDiagram_inl, SSet.comp_const, fixedFatConeUncurry_inl]
  · rw [← Category.assoc (fatJoinInr A K), fatJoinInr_map, Category.id_comp,
      fixedFatConeTimeDiagram_inr, fixedFatConeUncurry_inr]

/-- 概要：時間付き図式の一時間への制限は終点の錐の展開。
方針：円柱と左右の因子で比較し、円柱ではホモトピーの終点の式を使う。
規約：始点と終点は実際の固定頂点の錐の族で与える。
使われ方：Kerodon §4.6.6 の移送した族のホモトピーの終点。 -/
lemma fixedFatConeTimeDiagram_one {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} (f g : A ⟶ fixedEndpointFatConeSpace p x)
    (H : SSet.Homotopy (fixedFatConeUncurry f) (fixedFatConeUncurry g))
    (hx : (fatJoinInl A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ SSet.const x)
    (hp : (fatJoinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p) :
    fatJoinMap (SSet.ι₁ (X := A)) (𝟙 K) ≫ fixedFatConeTimeDiagram H hx hp =
      fixedFatConeUncurry g := by
  apply fatJoin_hom_ext
  · rw [← Category.assoc (fatJoinCylinder A K), fatJoinCylinder_map, Category.assoc,
      fixedFatConeTimeDiagram, fatJoinCylinder_desc,
      ← Category.assoc (fatJoinCylinderMap (SSet.ι₁ (X := A)) (𝟙 K)),
      fatJoinTimeInput_time_one, Category.assoc, H.h₁]
  · rw [← Category.assoc (fatJoinInl A K), fatJoinInl_map, Category.assoc,
      fixedFatConeTimeDiagram_inl, SSet.comp_const, fixedFatConeUncurry_inl]
  · rw [← Category.assoc (fatJoinInr A K), fatJoinInr_map, Category.id_comp,
      fixedFatConeTimeDiagram_inr, fixedFatConeUncurry_inr]

/-- 概要：両端を固定する図式のホモトピーは固定頂点の錐の族のホモトピーを与える。
方針：時間付き図式を固定頂点で curry し、展開の単射性で端点を計算する。
規約：充填性を要求しない構成である。
使われ方：Kerodon §4.6.6、7.4.1.6 の比較のホモトピー右逆。 -/
noncomputable def fixedFatConeHomotopyOfDiagram {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} (f g : A ⟶ fixedEndpointFatConeSpace p x)
    (H : SSet.Homotopy (fixedFatConeUncurry f) (fixedFatConeUncurry g))
    (hx : (fatJoinInl A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ SSet.const x)
    (hp : (fatJoinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p) :
    SSet.Homotopy f g where
  h := fixedFatConeCurry (fixedFatConeTimeDiagram H hx hp)
    (fixedFatConeTimeDiagram_inl H hx hp) (fixedFatConeTimeDiagram_inr H hx hp)
  h₀ := by
    apply fixedFatConeUncurry_injective p x
    rw [fixedFatConeUncurry_precomp, fixedFatConeUncurry_curry]
    exact fixedFatConeTimeDiagram_zero f g H hx hp
  h₁ := by
    apply fixedFatConeUncurry_injective p x
    rw [fixedFatConeUncurry_precomp, fixedFatConeUncurry_curry]
    exact fixedFatConeTimeDiagram_one f g H hx hp
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories.HomotopyLimits
