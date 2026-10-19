module

public import SerrePositivity.KST.Spectra.LimitRestrictionEquivalence
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceCylinderFunctorIso

/-!
概要：同値な形状への制限と同型な図式の間で、極限の存在を移す。
方針：錐の制限の trivial Kan 性から実際の錐を厳密に延長し、終対象性を保存・反映する。
規約：部分錐とその頂点を保持する。一般化は K-Sp 所有内に置く。
使われ方：Kerodon §7.1、HTT 4.2.4.1。任意の cospan の ∞ 引き戻し。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.DiagramLimitTransport

/-- 錐の形状を制限する実際の錐。 -/
def restrict {K L X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) (f : L ⟶ K) :
    JoinCone (f ≫ p) :=
  ⟨joinMap (𝟙 (Δ[0] : SSet.{u})) f ≫ c.val, by
    rw [← Category.assoc, joinInr_joinMap, Category.assoc, c.property]⟩

/-- 概要：錐を部分図式へ制限してもその頂点は変わらない。
方針：join の右包含と joinMap の可換性を用いる。
規約：実際の頂点の等号。使われ方：指定した極限対象を保つ延長。 -/
lemma vertex_restrict {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (f : L ⟶ K) : (restrict c f).vertex = c.vertex := by
  rw [JoinCone.vertex_eq, JoinCone.vertex_eq]
  change SSet.yonedaEquiv (joinInl Δ[0] L ≫ (joinMap (𝟙 Δ[0]) f ≫ c.val)) = _
  rw [← Category.assoc, joinInl_joinMap, Category.id_comp]

/-- 概要：trivial な slice 制限に沿って任意の錐を厳密に延長できる。
方針：制限射の切断を零単体に適用する。
規約：値域の quasicategory 性は不要。使われ方：普遍錐の存在の持ち上げ。 -/
lemma exists_cone_extension_of_trivialRestriction {K L X : SSet.{u}}
    (p : K ⟶ X) (f : L ⟶ K) [TrivialKanFibration (sliceOverRestrict p f)]
    (d : JoinCone (f ≫ p)) :
    ∃ c : JoinCone p, restrict c f = d ∧ c.vertex = d.vertex := by
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section (sliceOverRestrict p f)
  let c : JoinCone p := s.app (Opposite.op ⦋0⦌) d
  have h : restrict c f = d := by
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hs (Opposite.op ⦋0⦌)) d
  exact ⟨c, h, (vertex_restrict c f).symm.trans (congrArg JoinCone.vertex h)⟩

/-- 概要：trivial な slice 制限に沿って指定した極限錐を延長できる。
方針：厳密な錐の延長と終対象性の同値判定を合わせる。
規約：値域は quasicategory、部分錐と頂点を厳密に保持する。
使われ方：普遍錐を付加した図式の極限の構成。 -/
lemma exists_limitCone_extension_of_trivialRestriction {K L X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (f : L ⟶ K)
    [TrivialKanFibration (sliceOverRestrict p f)]
    (d : JoinCone (f ≫ p)) (hd : IsLimitCone d) :
    ∃ c : JoinCone p, IsLimitCone c ∧ restrict c f = d ∧ c.vertex = d.vertex := by
  obtain ⟨c, hc, hv⟩ := exists_cone_extension_of_trivialRestriction p f d
  refine ⟨c, ?_, hc, hv⟩
  apply ((qCatEquivalenceOfTrivialKanFibration (sliceOverRestrict p f)).isTerminalVertex_iff c).2
  change IsLimitCone (restrict c f)
  rw [hc]
  exact hd

/-- 概要：trivial な slice 制限は極限の存在を保ち反映する。
方針：順方向は終対象性の保存、逆方向は指定極限錐の延長。
規約：図式自体は任意。使われ方：有限極限の存在の帰納的構成。 -/
lemma hasLimit_iff_of_trivialRestriction {K L X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (f : L ⟶ K) [TrivialKanFibration (sliceOverRestrict p f)] :
    HasLimit p ↔ HasLimit (f ≫ p) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨restrict c f,
      ((qCatEquivalenceOfTrivialKanFibration (sliceOverRestrict p f)).isTerminalVertex_iff c).1 hc⟩
  · rintro ⟨d, hd⟩
    obtain ⟨c, hc, _⟩ := exists_limitCone_extension_of_trivialRestriction p f d hd
    exact ⟨c, hc⟩

/-- 同値な単射の形状への制限は極限の存在を保存・反映する。 -/
lemma hasLimit_iff_restrict {K L X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (f : L ⟶ K) [Mono f] (hf : IsPrecompositionEquivalence f) :
    HasLimit p ↔ HasLimit (f ≫ p) := by
  have := restriction_trivial p f hf
  exact hasLimit_iff_of_trivialRestriction p f

/-- 同値な図式の両端で、極限の存在は同値。 -/
lemma hasLimit_iff_equivalenceCylinder {K X : SSet.{u}} [Quasicategory X]
    (H : K ⊗ equivalenceInterval ⟶ X) :
    HasLimit (equivalenceCylinderEndpoint K false ≫ H) ↔
      HasLimit (equivalenceCylinderEndpoint K true ≫ H) :=
  (hasLimit_iff_restrict H _
    (isPrecompositionEquivalence_equivalenceCylinderEndpoint K false)).symm.trans
      (hasLimit_iff_restrict H _
        (isPrecompositionEquivalence_equivalenceCylinderEndpoint K true))

/-- 関手 quasicategory 内で同型な二つの図式は極限の存在が同値。 -/
lemma hasLimit_iff_of_functorIso {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (e : FunctorIso p q) : HasLimit p ↔ HasLimit q := by
  obtain ⟨H, h₀, h₁⟩ := exists_equivalenceCylinder_extension_of_functorIso e
  have h := hasLimit_iff_equivalenceCylinder H
  rw [h₀, h₁] at h
  exact h

/-- 同型な図式へ極限錐を移す際に、その頂点を保持できる。 -/
lemma exists_limitCone_of_functorIso {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (e : FunctorIso p q) (d : JoinCone q) (hd : IsLimitCone d) :
    ∃ c : JoinCone p, IsLimitCone c ∧ c.vertex = d.vertex := by
  obtain ⟨H, h₀, h₁⟩ := exists_equivalenceCylinder_extension_of_functorIso e
  have := restriction_trivial H (equivalenceCylinderEndpoint K true)
    (isPrecompositionEquivalence_equivalenceCylinderEndpoint K true)
  obtain ⟨c, hc, _, hv⟩ := exists_limitCone_extension_of_trivialRestriction H
    (equivalenceCylinderEndpoint K true) (d.cast h₁.symm) (hd.cast h₁.symm)
  have := restriction_trivial H (equivalenceCylinderEndpoint K false)
    (isPrecompositionEquivalence_equivalenceCylinderEndpoint K false)
  have hc₀ : IsLimitCone (restrict c (equivalenceCylinderEndpoint K false)) :=
    ((qCatEquivalenceOfTrivialKanFibration
      (sliceOverRestrict H (equivalenceCylinderEndpoint K false))).isTerminalVertex_iff c).1 hc
  exact ⟨(restrict c (equivalenceCylinderEndpoint K false)).cast h₀,
    hc₀.cast h₀, (vertex_restrict c _).trans hv⟩

end SerrePositivity.KST.Spectra.DiagramLimitTransport
