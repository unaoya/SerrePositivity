module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderSkeleton
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderSourceIso

/-!
概要：写像円柱比較を全ての骨格から始域の全体へ拡張する。
方針：相対セル複体の骨格列と包含を Over 圏へ持ち上げ、可算余極限の比較を使う。
規約：通常の単体集合の骨格と余極限を扱う。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、一般の始域への拡張。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet SSet.relativeCellComplexOfMono
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：構造射を持つ単体集合の相対骨格列を Over 圏の図式にする。
方針：相対セル複体の包含と構造射を合成し、Over.lift を使う。
規約：基準の射 i は単射。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、比較の骨格列の余極限。 -/
noncomputable def relativeJoinSkeletonDiagram {A X S : SSet.{u}}
    (i : A ⟶ X) [Mono i] (f : X ⟶ S) : ℕ ⥤ Over S :=
  Over.lift (SSet.relativeCellComplexOfMono i).F
    ((SSet.relativeCellComplexOfMono i).incl ≫ (Functor.const ℕ).map f)

/-- 概要：構造射を持つ始域の全体は Over 圏の骨格列の cocone の頂点。
方針：各骨格の包含を底上の射として使う。
規約：頂点の構造射は指定した f。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、全ての骨格の比較の貼り合わせ。 -/
noncomputable def relativeJoinSkeletonCocone {A X S : SSet.{u}}
    (i : A ⟶ X) [Mono i] (f : X ⟶ S) : Cocone (relativeJoinSkeletonDiagram i f) where
  pt := Over.mk f
  ι :=
    { app n := Over.homMk ((SSet.relativeCellComplexOfMono i).incl.app n) rfl
      naturality n m a := by
        apply Over.OverMorphism.ext
        change (SSet.relativeCellComplexOfMono i).F.map a ≫
          (SSet.relativeCellComplexOfMono i).incl.app m =
            (SSet.relativeCellComplexOfMono i).incl.app n
        have h := (SSet.relativeCellComplexOfMono i).incl.naturality a
        change (SSet.relativeCellComplexOfMono i).F.map a ≫
          (SSet.relativeCellComplexOfMono i).incl.app m =
            (SSet.relativeCellComplexOfMono i).incl.app n ≫ 𝟙 X at h
        exact h.trans (Category.comp_id _) }

/-- 概要：Over 圏の相対骨格の cocone は余極限。
方針：忘却関手で基礎の相対セル複体の余極限性を反映する。
規約：単体集合の余極限の主張。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、骨格から全体への比較の移送。 -/
noncomputable def relativeJoinSkeletonCocone_isColimit {A X S : SSet.{u}}
    (i : A ⟶ X) [Mono i] (f : X ⟶ S) : IsColimit (relativeJoinSkeletonCocone i f) := by
  apply isColimitOfReflects (Over.forget S)
  change IsColimit ⟨X, (SSet.relativeCellComplexOfMono i).incl⟩
  exact (SSet.relativeCellComplexOfMono i).isColimit

/-- 概要：Over 圏の骨格列の各遷移射は単射。
方針：部分複体の包含の左成分が単射であることを使う。
規約：隣り合う骨格間の射について述べる。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、可算余極限の比較の単射条件。 -/
instance relativeJoinSkeletonDiagram_map_mono {A X S : SSet.{u}}
    (i : A ⟶ X) [Mono i] (f : X ⟶ S) (n : ℕ) :
    Mono ((relativeJoinSkeletonDiagram i f).map (homOfLE (Nat.le_succ n))) := by
  have : Mono ((relativeJoinSkeletonDiagram i f).map (homOfLE (Nat.le_succ n))).left :=
    inferInstanceAs (Mono (r i n))
  exact Over.mono_of_mono_left _

/-- 概要：全ての相対骨格での円柱比較の同値条件から始域全体の比較が従う。
方針：構造射を保つ骨格列の可算余極限に比較の貼り合わせを適用する。
規約：骨格の基準の単射の始域は空とは限らない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、一般の始域の比較。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_of_skeletons
    {A X S : SSet.{u}} (i : A ⟶ X) [Mono i] (f : X ⟶ S)
    (h : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison ((skeletonOfMono i n).ι ≫ f))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison_of_sequential_colimit
    (relativeJoinSkeletonDiagram i f) (relativeJoinSkeletonCocone i f)
    (relativeJoinSkeletonCocone_isColimit i f)
  intro n
  exact h n

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
