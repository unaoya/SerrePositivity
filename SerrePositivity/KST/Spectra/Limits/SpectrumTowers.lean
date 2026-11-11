module

public import SerrePositivity.KST.Spectra.Limits.SpectrumTowerOmega
public import SerrePositivity.KST.Spectra.Limits.SpectrumTowerMonomorphisms
public import SerrePositivity.KST.Spectra.Limits.SpectrumHomFibrations

/-!
概要：L9 の段ごとに fibration の Ω スペクトルの塔の実際の ∞ 極限錐。
方針：段ごとの整合族の極限の単射構造射と Ω 条件を束ね、実際の豊穣 Hom で極限を検証する。
規約：対象の段を置換せず、元の塔の通常の厳密極限を使う。
使われ方：BF 1978 §2、HA §1.4.2、HTT 4.2.4.1、γ3c と L9 の Sp の塔。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：段ごとに fibration の Ω スペクトルの塔の実際の極限対象。
方針：元の段ごとの極限の Kan 列の単射な構造射と Ω 条件を束ねる。
規約：各段は点つき整合族の極限そのもの。
使われ方：Sp の塔の極限錐の頂点。 -/
def spectrumTower (X : ℕ → OmegaSpectrum.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    [∀ n k, Fibration ((d n).app k).right] : OmegaSpectrum.{u} := by
  let ds : ∀ n, KanSequence.Hom (X (n + 1)).toKanSequence (X n).toKanSequence :=
    fun n ↦ ⟨(d n).app, (d n).comm⟩
  have : ∀ n k, Fibration ((ds n).app k).right := fun n k ↦
    inferInstanceAs (Fibration ((d n).app k).right)
  let K := towerKanSequence (fun n ↦ (X n).toKanSequence) ds
  have hm (k : ℕ) : Mono (K.sigma k).right :=
    towerSequenceSigma_mono (fun n ↦ (X n).toKanSequence) ds
      (fun n k ↦ (X n).sigma_mono k) k
  have hΩ : K.OmegaCondition := towerKanSequence_omega
    (fun n ↦ (X n).toKanSequence) ds (fun n ↦ (X n).toKanSequence_omega)
  exact K.toOmegaSpectrum hm hΩ

/-- 概要：塔の極限スペクトルから各段への厳密な射影。
方針：Kan 列の極限の射影をスペクトルの射に束ねる。
規約：各段の射は元の点つき整合族の評価。
使われ方：Sp の極限錐の脚。 -/
def spectrumTowerProjection (X : ℕ → OmegaSpectrum.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    [∀ n k, Fibration ((d n).app k).right] (n : ℕ) : spectrumTower X d ⟶ X n where
  app k := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection (fun n ↦ ((X n).level k).space) (fun n ↦ (d n).app k) n
  comm k := by
    change _ = towerSequenceSigma _ _ k ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection _ _ n
    rw [towerSequenceSigma, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLift_projection]
    rfl

/-- 概要：極限スペクトルの射影は塔の遷移と可換。
方針：全段で点つき極限の射影の可換式を使う。
規約：元の Ω スペクトルの射の厳密な等式。
使われ方：塔の錐の自然性。 -/
lemma spectrumTowerProjection_comp (X : ℕ → OmegaSpectrum.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    [∀ n k, Fibration ((d n).app k).right] (n : ℕ) :
    spectrumTowerProjection X d (n + 1) ≫ d n = spectrumTowerProjection X d n := by
  apply OmegaSpectrum.Hom.ext
  intro k
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerProjection_comp (fun n ↦ ((X n).level k).space)
    (fun n ↦ (d n).app k) n

/-- 概要：実際の極限スペクトルを頂点とする通常の塔の錐。
方針：隣接段の可換な射影を自然変換へ延長する。
規約：添字は ℕ の反対圏。
使われ方：各段での通常の極限性の検証。 -/
def spectrumTowerOrdinaryCone (X : ℕ → OmegaSpectrum.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    [∀ n k, Fibration ((d n).app k).right] : Cone (Functor.ofOpSequence d) where
  pt := spectrumTower X d
  π := NatTrans.ofOpSequence (fun n ↦ spectrumTowerProjection X d n) (fun n ↦ by
    change 𝟙 _ ≫ spectrumTowerProjection X d n =
      spectrumTowerProjection X d (n + 1) ≫ (Functor.ofOpSequence d).map _
    rw [Category.id_comp, Functor.ofOpSequence_map_homOfLE_succ]
    exact (spectrumTowerProjection_comp X d n).symm)

/-- 概要：塔の錐を各スペクトル段へ評価すると通常の点つき極限錐。
方針：任意の錐の成分を整合族へ持ち上げ、全射影で一意性を示す。
規約：全自然数のスペクトル段で普遍性を構成する。
使われ方：豊穣 Hom の極限性へ渡す段ごとの条件。 -/
def spectrumTowerOrdinaryCone_level_isLimit (X : ℕ → OmegaSpectrum.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) [∀ n k, Fibration ((d n).app k).right] (k : ℕ) :
    IsLimit ((_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumLevelFunctor k).mapCone (spectrumTowerOrdinaryCone X d)) where
  lift c := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLift _ _ (fun n ↦ c.π.app (Opposite.op n)) (fun n ↦ by
    have h := c.w (homOfLE (Nat.le_succ n)).op
    rw [Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ] at h
    change c.π.app (Opposite.op (n + 1)) ≫ (d n).app k = c.π.app (Opposite.op n) at h
    exact h)
  fac c j := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLift_projection _ _ _ _ j.unop
  uniq c m hm := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLimit_hom_ext _ _ (fun n ↦ by
    exact (hm (Opposite.op n)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLift_projection (fun n ↦ ((X n).level k).space)
        (fun n ↦ (d n).app k) (fun n ↦ c.π.app (Opposite.op n)) _ n).symm)

/-- 概要：Sp の塔の小さい通常図式。
方針：自然数の反対圏の添字を Hom の宇宙へ持ち上げる。
規約：図式の隣接遷移は元のスペクトル射。
使われ方：coherent nerve の塔の図式。 -/
def spectrumTowerDiagram (X : ℕ → OmegaSpectrum.{u}) (d : ∀ n, X (n + 1) ⟶ X n) :
    AsSmall.{u} ℕᵒᵖ ⥤ OmegaSpectrum.{u} := AsSmall.down ⋙ Functor.ofOpSequence d

/-- 概要：小さい添字の塔の実際のスペクトル錐。
方針：通常の塔の錐を AsSmall の忘却に沿って制限する。
規約：頂点と各射影は変えない。
使われ方：γ3 の全 Hom による検出に渡す錐。 -/
def spectrumTowerCone (X : ℕ → OmegaSpectrum.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    [∀ n k, Fibration ((d n).app k).right] : Cone (spectrumTowerDiagram X d) :=
  (spectrumTowerOrdinaryCone X d).whisker AsSmall.down

/-- 概要：小さい添字の塔のスペクトル錐は各段で点つき極限。
方針：通常の塔の極限性を添字の圏同値で移す。
規約：全段で実際の普遍性を与える。
使われ方：実際の豊穣 Hom の極限性。 -/
def spectrumTowerCone_level_isLimit (X : ℕ → OmegaSpectrum.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) [∀ n k, Fibration ((d n).app k).right] (k : ℕ) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumLevelCone (spectrumTowerCone X d) k) :=
  (spectrumTowerOrdinaryCone_level_isLimit X d k).whiskerEquivalence
    (AsSmall.equiv : ℕᵒᵖ ≌ AsSmall.{u} ℕᵒᵖ).symm

local instance spectrumTowers_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

local instance spectrumTowers_locallyKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 概要：実際のスペクトルの塔の錐は全ての豊穣 Hom で極限。
方針：全段の極限性をスペクトルの Hom の普遍族の定理へ渡す。
規約：Hom の極限性を追加の前提として要求しない。
使われ方：HTT 4.2.4.1 の塔の移送定理の入力。 -/
def spectrumTowerCone_hom_isLimit (X : ℕ → OmegaSpectrum.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) [∀ n k, Fibration ((d n).app k).right] (Z : OmegaSpectrum.{u}) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (spectrumTowerCone X d) Z) :=
  _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumHomCone_isLimit_of_levelwise _ (spectrumTowerCone_level_isLimit X d) Z

/-- 概要：L9 の Ω スペクトルの塔の実際の coherent nerve の錐。
方針：段ごとに作った極限スペクトルの通常の錐を coherent nerve へ移す。
規約：頂点は実際の spectrumTower X d。
使われ方：Sp の塔の ∞ 極限錐。 -/
def spectrumTowerInfinityCone (X : ℕ → OmegaSpectrum.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    [∀ n k, Fibration ((d n).app k).right] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (spectrumTowerDiagram X d)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (spectrumTowerCone X d)

/-- 概要：段ごとに fibration のスペクトルの塔の実際の極限は Sp の ∞ 極限錐。
方針：全 Hom の通常の極限性と隣接遷移の fibration 性を塔の移送定理へ渡す。
規約：Hom の極限条件や Ω 条件を追加の前提に置かない。
使われ方：HTT 4.2.4.1 の双対、BF 1978 §2、HA §1.4.2、γ3c と L9。 -/
lemma spectrumTowerInfinityCone_isLimit (X : ℕ → OmegaSpectrum.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    [∀ n k, Fibration ((d n).app k).right] : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (spectrumTowerInfinityCone X d) := by
  have : ∀ (Z : OmegaSpectrum.{u}) (n : ℕ), Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (spectrumTowerDiagram X d) Z).map
        (AsSmall.up.map (homOfLE (Nat.le_succ n)).op)) := fun Z n ↦ by
    change Fibration (((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj
      (Opposite.op Z)).map ((Functor.ofOpSequence d).map (homOfLE (Nat.le_succ n)).op))
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumHomMap_fibration Z (d n)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_tower_homLimit (spectrumTowerCone X d)
    (spectrumTowerCone_hom_isLimit X d)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
