module

public import SerrePositivity.KST.Spectra.Limits.SpectrumTowerSequence
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SmashJointProjections

/-!
概要：塔の極限の懸垂構造射は元の構造射の単射性を保つ。
方針：全射影で右因子の整合族を識別し、smash の具体的表示で単射性を検査する。
規約：Kan 性や遷移の fibration 性を単射性の証明に使わない。
使われ方：BF 1978 §2、HTT 4.2.4.1、L9 の Ω スペクトルの塔の極限対象。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：元の構造射が全て単射なら塔の極限の構造射も各次数で単射。
方針：構造射の像の等号を全段へ射影し、単射性を戻して smash の射影族で識別する。
規約：遷移の fibration 性や列の Ω 条件は不要。
使われ方：Sp の塔の極限の構造射のモノ射性。 -/
lemma towerSequenceSigma_app_injective (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n))
    (hmono : ∀ n k, Mono ((X n).sigma k).right) (k : ℕ) (m : SimplexCategoryᵒᵖ) :
    Function.Injective ((towerSequenceSigma X d k).right.app m) := by
  intro s t h
  have hj : Function.Injective (fun b ↦ fun n ↦
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection (fun n ↦ ((X n).level k).space)
        (fun n ↦ (d n).app k) n).right.app m b) := by
    intro b b' hb
    apply Subtype.ext
    funext n
    exact congrFun hb n
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashMap_jointlyInjective (J := ℕ) PointedSimplicialSet.circle.{u}
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLimit (fun n ↦ ((X n).level k).space) (fun n ↦ (d n).app k))
    (fun n ↦ ((X n).level k).space)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection (fun n ↦ ((X n).level k).space)
      (fun n ↦ (d n).app k) n) m hj s t
  intro n
  have : Mono ((X n).sigma k).right := hmono n k
  apply (CategoryTheory.mono_iff_injective (((X n).sigma k).right.app m)).mp
    ((NatTrans.mono_iff_mono_app _).mp inferInstance m)
  have he := congrArg (fun z ↦
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection (fun n ↦ ((X n).level (k + 1)).space)
      (fun n ↦ (d n).app (k + 1)) n).right.app m z) h
  change ((towerSequenceSigma X d k ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection _ _ n).right.app m s) =
    ((towerSequenceSigma X d k ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection _ _ n).right.app m t) at he
  rw [towerSequenceSigma, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLift_projection] at he
  exact he

/-- 概要：単射な構造射を持つ Kan 列の塔の極限の構造射はモノ射。
方針：全単体次数の単射性を自然変換のモノ射の判定へ渡す。
規約：元の構造射の単射性だけを要求する。
使われ方：L9 の OmegaSpectrum の sigma_mono 条件。 -/
lemma towerSequenceSigma_mono (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n))
    (hmono : ∀ n k, Mono ((X n).sigma k).right) (k : ℕ) :
    Mono (towerSequenceSigma X d k).right := by
  rw [NatTrans.mono_iff_mono_app]
  intro m
  exact (CategoryTheory.mono_iff_injective _).mpr (towerSequenceSigma_app_injective X d hmono k m)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
