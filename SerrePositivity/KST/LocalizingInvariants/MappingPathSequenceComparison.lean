module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.MappingPathNaturality
public import SerrePositivity.KST.Spectra.MappingPathSequence
public import SerrePositivity.KST.Spectra.FiberOmegaSpectrum

/-!
概要：任意の厳密 BF 正方形を元の mapping path 列の射へ送る。
方針：path への後合成と源への射を、列の引き戻しの普遍性で貼る。
規約：始点・終点の両射影との厳密比較を保持。使われ方：fibration 置換の自然な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet

open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.MappingPathComparison
variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def pathPart : KanSequence.Hom (KanSequence.mappingPathSequence (sequenceHom p))
    Y'.toKanSequence.freePath :=
  (KanSequence.pullbackFirst (Y.toKanSequence.freePathEvaluation 1) (sequenceHom p)).comp
    (KanSequence.mappingPost _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} (sequenceHom b))

def sourcePart : KanSequence.Hom (KanSequence.mappingPathSequence (sequenceHom p))
    X'.toKanSequence := (KanSequence.mappingPathSource (sequenceHom p)).comp (sequenceHom a)

include h in
lemma condition (n : ℕ) : (pathPart p b).app n ≫ (Y'.toKanSequence.freePathEvaluation 1).app n =
    (sourcePart p a).app n ≫ (sequenceHom q).app n := by
  have hn : p.app n ≫ b.app n = a.app n ≫ q.app n :=
    congrArg (fun f => f.app n) h
  change (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint (Y.level n).space 1) (p.app n) ≫
    PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} (b.app n)) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint (Y'.level n).space 1 =
    (pullback.snd (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint (Y.level n).space 1) (p.app n) ≫ a.app n) ≫ q.app n
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.freePathEndpoint_naturality, ← Category.assoc,
    pullback.condition, Category.assoc, hn, Category.assoc]

def map : KanSequence.Hom (KanSequence.mappingPathSequence (sequenceHom p))
    (KanSequence.mappingPathSequence (sequenceHom q)) :=
  KanSequence.pullbackLift (Y'.toKanSequence.freePathEvaluation 1) (sequenceHom q)
    (pathPart p b) (sourcePart p a) (condition p q a b h)

lemma map_source (n : ℕ) : (map p q a b h).app n ≫
    (KanSequence.mappingPathSource (sequenceHom q)).app n =
      (KanSequence.mappingPathSource (sequenceHom p)).app n ≫ a.app n :=
  pullback.lift_snd _ _ _

lemma map_path (n : ℕ) : (map p q a b h).app n ≫
    (KanSequence.pullbackFirst (Y'.toKanSequence.freePathEvaluation 1) (sequenceHom q)).app n =
      (KanSequence.pullbackFirst (Y.toKanSequence.freePathEvaluation 1) (sequenceHom p)).app n ≫
        PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} (b.app n) := pullback.lift_fst _ _ _

lemma map_target (n : ℕ) : (map p q a b h).app n ≫
    (KanSequence.mappingPathTarget (sequenceHom q)).app n =
      (KanSequence.mappingPathTarget (sequenceHom p)).app n ≫ b.app n := by
  change (map p q a b h).app n ≫
    ((KanSequence.pullbackFirst (Y'.toKanSequence.freePathEvaluation 1) (sequenceHom q)).app n ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint (Y'.level n).space 0) = _
  rw [← Category.assoc, map_path, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.freePathEndpoint_naturality,
    ← Category.assoc]
  rfl

end SerrePositivity.KST.LocalizingInvariants.MappingPathComparison
