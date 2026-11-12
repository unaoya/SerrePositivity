module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells

/-!
概要：単体集合の射の像で覆った部分複体上での図式の接合。
方針：各単体の一つの前像を選び、重なりでの一致により値の選択独立性と自然性を示す。
規約：通常の単体集合の射の接合であり、∞ 圏の余極限を主張しない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、edgewise の境界の各面と右半分の接合。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：射の像の共通部分で一致する図式は、像の和である部分複体上へ接合できる。
方針：像の所属の証拠から前像を選び、写像の自然性と共通部分での一致で単体作用素との整合性を得る。
規約：各被覆射に単射性は要求しない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、境界データを延長領域上の一つの図式へまとめる。 -/
lemma exists_map_of_compatible_range_cover {I : Type v} {Y K : SSet.{u}}
    (X : I → SSet.{u}) (ι : ∀ i, X i ⟶ Y) (f : ∀ i, X i ⟶ K)
    (hc : ∀ (i j : I) (d : SimplexCategoryᵒᵖ) (x : (X i).obj d) (y : (X j).obj d),
      (ι i).app d x = (ι j).app d y → (f i).app d x = (f j).app d y) :
    ∃ F : ((⨆ i, Subcomplex.range (ι i) : Y.Subcomplex) : SSet.{u}) ⟶ K,
      ∀ i, Subcomplex.lift (ι i) (le_iSup (fun j ↦ Subcomplex.range (ι j)) i) ≫ F = f i := by
  classical
  let A : Y.Subcomplex := ⨆ i, Subcomplex.range (ι i)
  have he : ∀ (d : SimplexCategoryᵒᵖ) (s : (A : SSet.{u}).obj d),
      ∃ (i : I) (x : (X i).obj d), (ι i).app d x = s.val := by
    intro d s
    have hs := s.property
    change s.val ∈ (⨆ i, Subcomplex.range (ι i)).obj d at hs
    simpa only [Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.range_obj, Set.mem_range] using hs
  choose j x hx using he
  let F : (A : SSet.{u}) ⟶ K :=
    { app d := ↾fun s ↦ (f (j d s)).app d (x d s)
      naturality {d e} α := by
        apply ConcreteCategory.hom_ext
        intro s
        change (f (j e ((A : SSet.{u}).map α s))).app e (x e ((A : SSet.{u}).map α s)) =
          K.map α ((f (j d s)).app d (x d s))
        have hi : (ι (j e ((A : SSet.{u}).map α s))).app e (x e ((A : SSet.{u}).map α s)) =
            (ι (j d s)).app e ((X (j d s)).map α (x d s)) := by
          rw [hx, NatTrans.naturality_apply, hx]
          rfl
        exact (hc _ _ e _ _ hi).trans (NatTrans.naturality_apply (f (j d s)) α (x d s)) }
  refine ⟨F, ?_⟩
  intro i
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  change (f (j d ((Subcomplex.lift (ι i)
    (le_iSup (fun k ↦ Subcomplex.range (ι k)) i)).app d z))).app d
    (x d ((Subcomplex.lift (ι i)
      (le_iSup (fun k ↦ Subcomplex.range (ι k)) i)).app d z)) = (f i).app d z
  apply hc
  exact hx d _

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
