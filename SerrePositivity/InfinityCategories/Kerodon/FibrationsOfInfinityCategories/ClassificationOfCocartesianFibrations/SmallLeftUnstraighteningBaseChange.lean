module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSectionEquivalence

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallSimplicialMap
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps

/-!
概要：小さい coherent unstraightening の底の射に沿う比較と底変換。
方針：元の引き戻しの比較射を縮小し、同型と宇宙持ち上げの完全忠実性で普遍性を移す。
規約：構成は通常の単体集合の引き戻しを扱う。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、Corollary 5.6.0.6（Tag 028T）、分類の小さい代表における底変換。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：底の可換な射は小さい unstraightening の全空間の射を誘導する。
方針：元の引き戻しの比較射を縮小の同型で移す。
規約：h は図式の厳密な可換性を表す。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、小さい全空間の底の射に沿う比較。 -/
noncomputable def smallLeftUnstraighteningMap {B D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (α : B ⟶ D) (h : (SSet.uliftFunctor.{u + 1, u}).map α ≫ G = F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap F G ((SSet.uliftFunctor.{u + 1, u}).map α) h)

/-- 概要：小さい比較写像の持ち上げは元の比較写像と全空間の同型で可換。
方針：縮小した射の同型に関する自然性を適用する。
規約：小さい比較写像そのものについて述べる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、底変換の比較四角形の移送。 -/
lemma smallLeftUnstraighteningMap_naturality {B D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (α : B ⟶ D) (h : (SSet.uliftFunctor.{u + 1, u}).map α ≫ G = F) :
    (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningMap F G α h) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso G).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso F).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap F G ((SSet.uliftFunctor.{u + 1, u}).map α) h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialMap_naturality _

/-- 概要：小さい unstraightening の比較写像は元の底の射を被覆する。
方針：宇宙を持ち上げた後に全空間の同型を使って射影の等式を計算する。
規約：射影は小さい底に値を取る。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、小さい底変換の四角形の可換性。 -/
lemma smallLeftUnstraighteningMap_projection {B D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (α : B ⟶ D) (h : (SSet.uliftFunctor.{u + 1, u}).map α ≫ G = F) :
    smallLeftUnstraighteningMap F G α h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection G =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F ≫ α := by
  apply (SSet.uliftFunctor.{u + 1, u}).map_injective
  simp only [Functor.map_comp]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso_projection G, ← Category.assoc,
    smallLeftUnstraighteningMap_naturality, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap_projection, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso_projection F]

/-- 概要：小さい unstraightening の底の比較四角形は引き戻し。
方針：元の引き戻しを全空間の同型で移し、宇宙持ち上げの完全忠実性で反映する。
規約：底や図式に充填性を仮定しない。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、Corollary 5.6.0.6（Tag 028T）、小さい代表の厳密な底変換。 -/
lemma smallLeftUnstraighteningMap_isPullback {B D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (α : B ⟶ D) (h : (SSet.uliftFunctor.{u + 1, u}).map α ≫ G = F) :
    IsPullback (smallLeftUnstraighteningMap F G α h) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection G) α := by
  apply IsPullback.of_map (SSet.uliftFunctor.{u + 1, u})
    (smallLeftUnstraighteningMap_projection F G α h)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap_isPullback F G ((SSet.uliftFunctor.{u + 1, u}).map α) h).of_iso'
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso G) (Iso.refl _) (Iso.refl _)
  · exact (smallLeftUnstraighteningMap_naturality F G α h).symm
  · simpa only [Iso.refl_hom, Category.comp_id] using _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso_projection F
  · simpa only [Iso.refl_hom, Category.comp_id] using _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso_projection G
  · simp only [Category.id_comp, Category.comp_id, Iso.refl_hom]

/-- 概要：制限した図式の小さい unstraightening は元の小さい射影の底変換と同型。
方針：小さい比較四角形の引き戻しの普遍性を使う。
規約：図式の制限では底の射 k を持ち上げて前合成する。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、小さい left fibration としての底変換の比較。 -/
noncomputable def smallLeftUnstraighteningBaseChangeIso {B D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (k : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening ((SSet.uliftFunctor.{u + 1, u}).map k ≫ F) ≅
      pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) k :=
  (smallLeftUnstraighteningMap_isPullback
    ((SSet.uliftFunctor.{u + 1, u}).map k ≫ F) F k rfl).isoPullback

/-- 概要：恒等の底の射による小さい unstraightening の比較射は恒等射。
方針：元の比較射の恒等則と縮小による恒等射保存を使う。
規約：図式 F 自体を固定する。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、小さい構成の底の射に対する単位則。 -/
lemma smallLeftUnstraighteningMap_id {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    smallLeftUnstraighteningMap F F (𝟙 B) (by simp) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F) := by
  unfold smallLeftUnstraighteningMap
  simp only [(SSet.uliftFunctor.{u + 1, u}).map_id,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap_id, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialMap_id]
  rfl

/-- 概要：底の射の合成による小さい unstraightening の比較射は比較射の合成。
方針：元の引き戻しの比較射と縮小した射の合成則を合わせる。
規約：α の後に β を合成する。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、小さい構成の底の射に対する関手性。 -/
lemma smallLeftUnstraighteningMap_comp {B D E : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (H : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (α : B ⟶ D) (β : D ⟶ E)
    (hα : (SSet.uliftFunctor.{u + 1, u}).map α ≫ G = F)
    (hβ : (SSet.uliftFunctor.{u + 1, u}).map β ≫ H = G) :
    smallLeftUnstraighteningMap F H (α ≫ β)
        (by rw [Functor.map_comp, Category.assoc, hβ, hα]) =
      smallLeftUnstraighteningMap F G α hα ≫ smallLeftUnstraighteningMap G H β hβ := by
  unfold smallLeftUnstraighteningMap
  simp only [(SSet.uliftFunctor.{u + 1, u}).map_comp]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap_comp F G H
    ((SSet.uliftFunctor.{u + 1, u}).map α) ((SSet.uliftFunctor.{u + 1, u}).map β) hα hβ,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialMap_comp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
