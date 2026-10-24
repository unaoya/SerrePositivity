module
public import SerrePositivity.InfinityCategories.Core.ColimitCoconeRestriction
public import SerrePositivity.InfinityCategories.Core.InitialEquivalence
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-! General declarations moved verbatim from their original modules. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
open scoped Simplicial

/-- 概要：余錐を部分図式へ制限してもその頂点は変わらない。
方針：join の右包含と joinMap の可換性を用いる。
規約：実際の頂点の等号。使われ方：指定した余極限対象を保つ延長。 -/
lemma JoinCocone.vertex_restrict {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (f : L ⟶ K) : (c.restrict f).vertex = c.vertex := by
  rw [JoinCocone.vertex_eq, JoinCocone.vertex_eq]
  change SSet.yonedaEquiv (joinInr L Δ[0] ≫ (joinMap f (𝟙 Δ[0]) ≫ c.val)) = _
  rw [← Category.assoc, joinInr_joinMap, Category.id_comp]


/-- 概要：trivial な coslice 制限に沿って任意の余錐を厳密に延長できる。
方針：制限射の切断を零単体に適用する。
規約：値域の quasicategory 性は不要。使われ方：普遍余錐の存在の持ち上げ。 -/
lemma exists_cocone_extension_of_trivialRestriction {K L X : SSet.{u}}
    (p : K ⟶ X) (f : L ⟶ K) [TrivialKanFibration (sliceUnderRestrict p f)]
    (d : JoinCocone (f ≫ p)) :
    ∃ c : JoinCocone p, c.restrict f = d ∧ c.vertex = d.vertex := by
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section (sliceUnderRestrict p f)
  let c : JoinCocone p := s.app (Opposite.op ⦋0⦌) d
  have h : c.restrict f = d := by
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hs (Opposite.op ⦋0⦌)) d
  exact ⟨c, h, (c.vertex_restrict f).symm.trans (congrArg JoinCocone.vertex h)⟩


/-- 概要：trivial な coslice 制限に沿って指定した余極限余錐を延長できる。
方針：厳密な余錐の延長と始対象性の同値判定を合わせる。
規約：値域は quasicategory、部分余錐と頂点を厳密に保持する。
使われ方：普遍余錐を付加した図式の余極限の構成。 -/
lemma exists_colimitCocone_extension_of_trivialRestriction {K L X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (f : L ⟶ K)
    [TrivialKanFibration (sliceUnderRestrict p f)]
    (d : JoinCocone (f ≫ p)) (hd : IsColimitCone d) :
    ∃ c : JoinCocone p, IsColimitCone c ∧ c.restrict f = d ∧ c.vertex = d.vertex := by
  obtain ⟨c, hc, hv⟩ := exists_cocone_extension_of_trivialRestriction p f d
  refine ⟨c, ?_, hc, hv⟩
  apply ((qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict p f)).isInitialVertex_iff c).2
  change IsColimitCone (c.restrict f)
  rw [hc]
  exact hd


/-- 概要：trivial な coslice 制限は余極限の存在を保ち反映する。
方針：順方向は始対象性の保存、逆方向は指定余極限余錐の延長。
規約：図式自体は任意。使われ方：有限余極限の存在の帰納的構成。 -/
lemma hasColimit_iff_of_trivialRestriction {K L X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (f : L ⟶ K) [TrivialKanFibration (sliceUnderRestrict p f)] :
    HasColimit p ↔ HasColimit (f ≫ p) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.restrict f,
      ((qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict p f)).isInitialVertex_iff c).1 hc⟩
  · rintro ⟨d, hd⟩
    obtain ⟨c, hc, _⟩ := exists_colimitCocone_extension_of_trivialRestriction p f d hd
    exact ⟨c, hc⟩


end SerrePositivity.InfinityCategories
