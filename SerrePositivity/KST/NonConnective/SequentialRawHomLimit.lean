module

public import SerrePositivity.KST.NonConnective.SequentialHomLimitCompatibility

/-!
概要：逐次 BF 余極限に対する全 Raw Hom の厳密な極限性。
方針：各段の普遍族を全整合写像空間へ束ね、各段の Hom 極限で一意性を示す。
規約：通常の IsLimit。BK end への比較同値は別に証明する。
使われ方：同じ実 Sp 余錐の ∞ 普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 同じ逐次 BF 余錐の反対へ、固定 Kan 列への全 Raw Hom を適用した錐。 -/
def sequentialRawHomCone (D : SpectrumSequence.{u}) (Y : KanSequence.{u}) :
    Cone (sequentialRawHomDiagram D Y) :=
  (RawSpectrumMapping.sourceFunctor Y ⋙ PointedSimplicialSet.forget).mapCone
    (sequentialLevelColimitCocone D).op

/-- 元の全 Raw Hom 図式の厳密錐を、余極限源からの全整合写像空間へ持ち上げる。 -/
def sequentialRawHomLimitLift (D : SpectrumSequence.{u}) (Y : KanSequence.{u})
    (s : Cone (sequentialRawHomDiagram D Y)) :
    s.pt ⟶ RawSpectrumMapping.space (sequentialLevelColimitSpectrum D) Y :=
  RawSpectrumMapping.lift _ Y (sequentialHomLimitFamily D Y s)
    (sequentialHomLimitFamily_condition D Y s)

/-- 全 Hom の普遍射は、各スペクトル段で元の一段の普遍族を回収する。 -/
lemma sequentialRawHomLimitLift_evaluation (D : SpectrumSequence.{u}) (Y : KanSequence.{u})
    (s : Cone (sequentialRawHomDiagram D Y)) (k : ℕ) :
    sequentialRawHomLimitLift D Y s ≫
      RawSpectrumMapping.evaluation (sequentialLevelColimitSpectrum D) Y k =
        sequentialHomLimitFamily D Y s k :=
  RawSpectrumMapping.lift_evaluation _ _ _ _ k

/-- 全 Hom の普遍射の各入力への制限は、元の厳密錐の同じ成分。 -/
lemma sequentialRawHomLimitLift_fac (D : SpectrumSequence.{u}) (Y : KanSequence.{u})
    (s : Cone (sequentialRawHomDiagram D Y)) (a : SequentialIndex.{u}ᵒᵖ) :
    sequentialRawHomLimitLift D Y s ≫ (sequentialRawHomCone D Y).π.app a = s.π.app a := by
  apply RawSpectrumMapping.hom_ext (D.obj a.unop) Y
  intro k
  change (sequentialRawHomLimitLift D Y s ≫
    RawSpectrumMapping.pre (sequentialLevelColimitInjection D a.unop) Y) ≫ _ = _
  rw [Category.assoc, RawSpectrumMapping.pre_evaluation, ← Category.assoc,
    sequentialRawHomLimitLift_evaluation]
  exact sequentialHomLimitFamily_fac D Y s k a

/-- 元の逐次 BF 余錐の全反変 Raw Hom は、単体集合の通常の極限錐。 -/
def sequentialRawHomIsLimit (D : SpectrumSequence.{u}) (Y : KanSequence.{u}) :
    IsLimit (sequentialRawHomCone D Y) where
  lift := sequentialRawHomLimitLift D Y
  fac := sequentialRawHomLimitLift_fac D Y
  uniq s m hm := by
    change s.pt ⟶ RawSpectrumMapping.space (sequentialLevelColimitSpectrum D) Y at m
    apply RawSpectrumMapping.hom_ext (sequentialLevelColimitSpectrum D) Y
    intro k
    rw [sequentialRawHomLimitLift_evaluation]
    apply (sequentialLevelHomIsLimit D Y k).hom_ext
    intro a
    have hπ : (sequentialLevelHomCone D Y k).π.app a =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (colimit.ι (OmegaSpectrum.levelDiagram D k) a.unop)
          (Y.level k).space :=
      (congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre _ _)).symm
    rw [hπ]
    have h := congrArg (· ≫ RawSpectrumMapping.evaluation (D.obj a.unop) Y k) (hm a)
    change (m ≫ RawSpectrumMapping.pre (sequentialLevelColimitInjection D a.unop) Y) ≫ _ = _ at h
    rw [Category.assoc, RawSpectrumMapping.pre_evaluation, ← Category.assoc] at h
    exact h.trans (sequentialHomLimitFamily_fac D Y s k a).symm

end SerrePositivity.KST.NonConnective
