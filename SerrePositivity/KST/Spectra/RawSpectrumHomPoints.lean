module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingPointed
public import SerrePositivity.KST.Spectra.SpectrumMorphisms

/-!
概要：任意の Kan 列への厳密な列射を、元の全 Hom の点つき単位パラメータへ移す。
方針：各段の curry' が同じ構造条件を満たすことを確認し、元の pointedLift を使う。
規約：標的の Ω 条件や単射構造は不要。使われ方：全パラメータの列の厳密化の出力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 点つき射の厳密な構造正方形は、同じ curry' の Hom 正方形を与える。 -/
lemma homPoint_step {U V U' V' : PointedSimplicialSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension U ⟶ U') (t : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension V ⟶ V') (f : U ⟶ V) (g : U' ⟶ V')
    (h : PointedSimplicialSet.circle.{u} ◁ f ≫ t = s ≫ g) :
    curry' g ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed s V' =
      curry' f ≫ suspensionHom U V ≫ PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension U) t := by
  rw [PointedMapping.curry'_pre, ← Category.assoc, suspensionHom_curry']
  exact (congrArg curry' h.symm).trans (curry'_ihom_map _ _).symm

/-- 任意の Kan 列への厳密な列射の各段は、同じ Hom の単位パラメータで整合する。 -/
lemma homPoint_condition (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (f : KanSequence.Hom X.toKanSequence Y) (n : ℕ) :
    curry' (f.app (n + 1)) ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space =
      curry' (f.app n) ≫ pointedStep X Y n := by
  exact homPoint_step (X.sigma n) (Y.sigma n) (f.app n) (f.app (n + 1)) (f.comm n)

/-- 元の列射を、同じ全 Hom 内の点つき零次球面からの射として読む。 -/
def homPoint (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (f : KanSequence.Hom X.toKanSequence Y) :
    𝟙_ PointedSimplicialSet.{u} ⟶ pointedSpace X Y :=
  pointedLift X Y (fun n ↦ curry' (f.app n))
    (fun n ↦ congrArg Under.Hom.right (homPoint_condition X Y f n))

/-- 元の列射の単位パラメータの段評価は、同じ元の段射の curry'。 -/
@[reassoc]
lemma homPoint_evaluation (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (f : KanSequence.Hom X.toKanSequence Y) (n : ℕ) :
    homPoint X Y f ≫ pointedEvaluation X Y n = curry' (f.app n) :=
  pointedLift_evaluation _ _ _ _ _

end SerrePositivity.KST.Spectra.RawSpectrumMapping
