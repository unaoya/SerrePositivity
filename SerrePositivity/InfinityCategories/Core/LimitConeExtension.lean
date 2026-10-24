module

public import SerrePositivity.InfinityCategories.Core.SliceRestrictionEquivalence
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.Limit

/-!
概要：slice の自明な制限に沿う極限錐の厳密な延長。
方針：制限射の切断で錐を延長し、終対象性を同値に沿って反映する。
規約：元の部分錐と頂点を等号で保持する。
使われ方：Cat_∞ の path 置換後の極限錐を元の図式へ輸送する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：錐を元の図式の部分形状へ制限する。
方針：slice の制限射を零単体へ適用する。
規約：指定された形状の射そのものを使う。
使われ方：可逆円柱の両端での極限錐の比較。 -/
def restrictJoinCone {K L X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) (f : L ⟶ K) :
    JoinCone (f ≫ p) := (sliceOverRestrict p f).app (Opposite.op ⦋0⦌) c
/-- 概要：形状の制限は錐の頂点を変えない。
方針：join の左包含と joinMap の可換性を使う。
規約：頂点は同型だけでなく厳密に等しい。
使われ方：指定した引き戻し対象を保つ図式の輸送。 -/
lemma restrictJoinCone_vertex {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (f : L ⟶ K) : (restrictJoinCone c f).vertex = c.vertex := by
  rw [JoinCone.vertex_eq, JoinCone.vertex_eq]
  change SSet.yonedaEquiv (joinInl Δ[0] L ≫ (joinMap (𝟙 Δ[0]) f ≫ c.val)) = _
  rw [← Category.assoc, joinInl_joinMap, Category.id_comp]

/-- 概要：trivial な slice 制限に沿って任意の錐を厳密に延長できる。
方針：制限射の切断を零単体に適用する。
規約：値域の quasicategory 性は不要。
使われ方：普遍錐の存在の持ち上げ。 -/
lemma exists_cone_extension_of_trivialRestriction {K L X : SSet.{u}}
    (p : K ⟶ X) (f : L ⟶ K) [TrivialKanFibration (sliceOverRestrict p f)]
    (d : JoinCone (f ≫ p)) :
    ∃ c : JoinCone p, restrictJoinCone c f = d ∧ c.vertex = d.vertex := by
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section (sliceOverRestrict p f)
  let c : JoinCone p := s.app (Opposite.op ⦋0⦌) d
  have h : restrictJoinCone c f = d := by
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hs (Opposite.op ⦋0⦌)) d
  exact ⟨c, h, (restrictJoinCone_vertex c f).symm.trans (congrArg JoinCone.vertex h)⟩

/-- 概要：trivial な slice 制限に沿って指定した極限錐を延長できる。
方針：厳密な錐の延長と終対象性の同値判定を合わせる。
規約：値域は quasicategory、部分錐と頂点を厳密に保持する。
使われ方：普遍錐を付加した図式の極限の構成。 -/
lemma exists_limitCone_extension_of_trivialRestriction {K L X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (f : L ⟶ K)
    [TrivialKanFibration (sliceOverRestrict p f)]
    (d : JoinCone (f ≫ p)) (hd : IsLimitCone d) :
    ∃ c : JoinCone p, IsLimitCone c ∧ restrictJoinCone c f = d ∧ c.vertex = d.vertex := by
  obtain ⟨c, hc, hv⟩ := exists_cone_extension_of_trivialRestriction p f d
  refine ⟨c, ?_, hc, hv⟩
  apply ((qCatEquivalenceOfTrivialKanFibration (sliceOverRestrict p f)).isTerminalVertex_iff c).2
  change IsLimitCone (restrictJoinCone c f)
  rw [hc]
  exact hd

end SerrePositivity.InfinityCategories
