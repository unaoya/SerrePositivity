module

public import SerrePositivity.InfinityCategories.F1.RelativeJoinCylinderExtension
public import SerrePositivity.InfinityCategories.F1.StdSimplexFunctorRigidity

/-!
概要：区間への射影を保つ写像円柱の射を relative join 全体へ延長する。
方針：標準単体への射の剛性で、延長の区間への射影を円柱上の等式から復元する。
規約：構造射は単射、全空間の標的は quasicategory。
使われ方：Kerodon Theorem 5.2.4.1、区間上の全空間比較の射の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：写像円柱の区間への標準射影。
方針：終域を係数とする区間へ写し、係数を忘れる。
規約：円柱部分では時間を保ち、終域部分では時刻一となる。
使われ方：Kerodon Theorem 5.2.4.1、円柱上の底の条件。 -/
noncomputable def mappingCylinderIntervalProjection {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout (prismEndpoint 1 X) f ⟶ (Δ[1] : SSet.{u}) :=
  mappingCylinderPrismMap f ≫ fst Δ[1] Y

/-- 概要：写像円柱の射影は円柱部分では区間の第一射影。
方針：pushout の計算則と区間との積の自然性を使う。
規約：係数 X は忘れる。
使われ方：Kerodon Theorem 5.2.4.1、prism 上の底の整合性。 -/
lemma mappingCylinderIntervalProjection_inl {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout.inl (prismEndpoint 1 X) f ≫ mappingCylinderIntervalProjection f = fst Δ[1] X := by
  rw [mappingCylinderIntervalProjection, ← Category.assoc, mappingCylinderPrismMap,
    pushout.inl_desc, whiskerLeft_fst]

/-- 概要：写像円柱の射影は終域部分を時刻一へ送る。
方針：pushout の計算則で終点の prism 包含を取り出す。
規約：右辺は終点の零単体への定値射。
使われ方：Kerodon Theorem 5.2.4.1、終域上の底の整合性。 -/
lemma mappingCylinderIntervalProjection_inr {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout.inr (prismEndpoint 1 X) f ≫ mappingCylinderIntervalProjection f =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  rw [mappingCylinderIntervalProjection, ← Category.assoc, mappingCylinderPrismMap,
    pushout.inr_desc]
  rfl

/-- 概要：円柱比較は区間への射影を保つ。
方針：係数付き区間への比較の計算から係数を忘れる。
規約：relative join の射影は既存の relativeJoinProjection。
使われ方：Kerodon Theorem 5.2.4.1、比較を区間上の射として扱う。 -/
lemma relativeJoinCylinderComparison_intervalProjection {X Y : SSet.{u}} (f : X ⟶ Y) :
    relativeJoinCylinderComparison f ≫ relativeJoinProjection f (𝟙 Y) =
      mappingCylinderIntervalProjection f := by
  rw [relativeJoinProjection, ← Category.assoc, relativeJoinCylinderComparison_prismMap]
  rfl

/-- 概要：円柱上で区間への射影を保つ延長は全体でも射影を保つ。
方針：円柱比較による前合成の同値と標準単体への射の剛性を使う。
規約：既存の延長 G に追加の選択や修正を加えない。
使われ方：Kerodon Theorem 5.2.4.1、延長した比較の底上の可換性。 -/
lemma relativeJoinCylinder_extension_intervalProjection {X Y E : SSet.{u}}
    (f : X ⟶ Y) (p : E ⟶ (Δ[1] : SSet.{u}))
    (u : pushout (prismEndpoint 1 X) f ⟶ E) (hu : u ≫ p = mappingCylinderIntervalProjection f)
    (G : relativeJoin f (𝟙 Y) ⟶ E) (hG : relativeJoinCylinderComparison f ≫ G = u) :
    G ≫ p = relativeJoinProjection f (𝟙 Y) := by
  apply (isPrecompositionEquivalence_relativeJoinCylinderComparison f).stdSimplex_hom_ext
  rw [← Category.assoc, hG, hu, relativeJoinCylinderComparison_intervalProjection]

/-- 概要：単射の円柱上の射は区間への射影を保ったまま relative join 全体へ延長できる。
方針：円柱上の射の延長を選び、区間への射影の剛性を適用する。
規約：標的 E のみ quasicategory とする。
使われ方：Kerodon Theorem 5.2.4.1、fiber ごとの比較に使う全空間の射。 -/
lemma relativeJoinCylinder_extension_over_interval_exists {X Y E : SSet.{u}}
    (f : X ⟶ Y) [Mono f] [Quasicategory E] (p : E ⟶ (Δ[1] : SSet.{u}))
    (u : pushout (prismEndpoint 1 X) f ⟶ E) (hu : u ≫ p = mappingCylinderIntervalProjection f) :
    ∃ G : relativeJoin f (𝟙 Y) ⟶ E,
      relativeJoinCylinderComparison f ≫ G = u ∧ G ≫ p = relativeJoinProjection f (𝟙 Y) := by
  obtain ⟨G, hG⟩ := relativeJoinCylinder_extension_exists f u
  exact ⟨G, hG, relativeJoinCylinder_extension_intervalProjection f p u hu G hG⟩

/-- 概要：区間上の整合する prism と終域の二射を relative join 全体へ延長できる。
方針：二射を円柱上で貼り、区間を保つ延長を選ぶ。
規約：prism は時間を保ち、終域は時刻一に写る。
使われ方：Kerodon Theorem 5.2.4.1、relative join を通した比較の構成。 -/
lemma relativeJoin_extension_of_prism_over_interval {X Y E : SSet.{u}}
    (f : X ⟶ Y) [Mono f] [Quasicategory E] (p : E ⟶ (Δ[1] : SSet.{u}))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (g : Y ⟶ E)
    (w : prismEndpoint 1 X ≫ H = f ≫ g) (hH : H ≫ p = fst Δ[1] X)
    (hg : g ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :
    ∃ G : relativeJoin f (𝟙 Y) ⟶ E,
      relativeJoinPrism f ≫ G = H ∧ relativeJoinInr f (𝟙 Y) ≫ G = g ∧
        G ≫ p = relativeJoinProjection f (𝟙 Y) := by
  have hu : pushout.desc H g w ≫ p = mappingCylinderIntervalProjection f := by
    apply pushout.hom_ext
    · rw [← Category.assoc, pushout.inl_desc, hH, mappingCylinderIntervalProjection_inl]
    · rw [← Category.assoc, pushout.inr_desc, hg, mappingCylinderIntervalProjection_inr]
  obtain ⟨G, hG, hp⟩ := relativeJoinCylinder_extension_over_interval_exists f p (pushout.desc H g w) hu
  refine ⟨G, ?_, ?_, hp⟩
  · have he := congrArg (fun q ↦ pushout.inl (prismEndpoint 1 X) f ≫ q) hG
    simpa only [← Category.assoc, relativeJoinCylinderComparison_inl, pushout.inl_desc] using he
  · have he := congrArg (fun q ↦ pushout.inr (prismEndpoint 1 X) f ≫ q) hG
    simpa only [← Category.assoc, relativeJoinCylinderComparison_inr, pushout.inr_desc] using he

end SerrePositivity.InfinityCategories
