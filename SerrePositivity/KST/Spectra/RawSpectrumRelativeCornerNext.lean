module

public import SerrePositivity.KST.Spectra.RawSpectrumRelativeCornerStep
public import SerrePositivity.KST.Spectra.TriangleMappingPost

/-!
概要：二変数 Raw Hom corner の持ち上げを次のスペクトル段へ延長する。
方針：相対 latching の Hom の実引き戻しへ前段と元の源を貼り、標的射影と同時に充填する。
規約：既定の部分族・元の源・前段・射影先の四条件を保持する。
使われ方：全段の二変数 corner の全単射 RLP の帰納工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.KST.NonConnective
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 概要：相対 latching と標的射影を同時に指定した次段の実持ち上げ。
方針：元の二部分の族を latching 対象へ貼り、同じ標的射影の corner を充填する。
規約：全ての射は元の点つき Hom の全パラメータ族。
使われ方：二変数 Raw Hom corner の全段帰納。 -/
lemma relativeCornerNext {X R : OmegaSpectrum.{u}} (i : X ⟶ R)
    (hi : IsSequentialRelativeCofibration i) (n : ℕ)
    {E Z : PointedSimplicialSet.{u}} (p : E ⟶ Z)
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right)
    {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
    (a : T ⟶ (PointedObject.basedHom (R.level (n + 1)).space E).right)
    (b : U ⟶ (PointedObject.basedHom (R.level (n + 1)).space Z).right)
    (v : U ⟶ (PointedObject.basedHom (X.level (n + 1)).space E).right)
    (u : U ⟶ (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (R.level n).space) E).right)
    (huv : u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ i.app n) E =
      v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) E)
    (hu : j ≫ u = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (R.sigma n) E)
    (hv : j ≫ v = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (i.app (n + 1)) E)
    (ha : a ≫ (PointedObject.basedHomMap (R.level (n + 1)).space p).right = j ≫ b)
    (hub : u ≫ (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (R.level n).space) p).right =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (R.sigma n) Z)
    (hvb : v ≫ (PointedObject.basedHomMap (X.level (n + 1)).space p).right =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (i.app (n + 1)) Z) :
    ∃ l : U ⟶ (PointedObject.basedHom (R.level (n + 1)).space E).right,
      j ≫ l = a ∧
      l ≫ (PointedObject.basedHomMap (R.level (n + 1)).space p).right = b ∧
      l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (R.sigma n) E = u ∧
      l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (i.app (n + 1)) E = v := by
  let hE := sequentialLatchingHom_isPullback i n E
  let hZ := sequentialLatchingHom_isPullback i n Z
  let c := hE.lift u v huv
  have hleft : c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
      (pushout.inl (PointedSimplicialSet.circle.{u} ◁ i.app n) (X.sigma n)) E = u :=
    hE.lift_fst _ _ _
  have hright : c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
      (pushout.inr (PointedSimplicialSet.circle.{u} ◁ i.app n) (X.sigma n)) E = v :=
    hE.lift_snd _ _ _
  have hc : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (sequentialRelativeLatchingMap i n) E = j ≫ c := by
    apply hE.hom_ext
    · simpa only [Category.assoc, sequentialLatchingHom_pre_inl, hleft] using hu.symm
    · simpa only [Category.assoc, sequentialLatchingHom_pre_inr, hright] using hv.symm
  have hcb : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (sequentialRelativeLatchingMap i n) Z =
      c ≫ (PointedObject.basedHomMap _ p).right := by
    apply hZ.hom_ext
    · rw [Category.assoc, sequentialLatchingHom_pre_inl,
        Category.assoc, ← PointedMapping.pre_post_comm, ← Category.assoc, hleft]
      exact hub.symm
    · rw [Category.assoc, sequentialLatchingHom_pre_inr,
        Category.assoc, ← PointedMapping.pre_post_comm, ← Category.assoc, hright]
      exact hvb.symm
  let : Mono (sequentialRelativeLatchingMap i n).right := hi.2 n
  obtain ⟨l, hl, hb, hc⟩ := PointedMapping.corner_family_lift
    (sequentialRelativeLatchingMap i n) p hp j a b c hcb ha hc
  refine ⟨l, hl, hb, ?_, ?_⟩
  · rw [← sequentialLatchingHom_pre_inl i n E, ← Category.assoc, hc, hleft]
  · rw [← sequentialLatchingHom_pre_inr i n E, ← Category.assoc, hc, hright]

end SerrePositivity.KST.Spectra.RawSpectrumMapping
