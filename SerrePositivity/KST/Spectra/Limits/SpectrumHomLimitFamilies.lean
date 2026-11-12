module

public import SerrePositivity.KST.Spectra.Limits.SpectrumMappingDiagram

/-!
概要：段ごとの極限を持つ Ω スペクトルの錐に、全 Hom パラメータの普遍的な各段の族を作る。
方針：点つき写像空間の極限保存と評価の自然変換を使う。
規約：各段の極限性は点つき単体集合の圏で指定する。
使われ方：HTT 4.2.4.1、BF 1978 §2、γ3c の Sp の Hom の極限性の検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HomotopyLimits

noncomputable section
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

variable {I : Type u} [SmallCategory I] {F : I ⥤ OmegaSpectrum.{u}}

/-- 概要：スペクトルの錐を指定段の点つき単体集合の錐へ評価する。
方針：指定段の評価関手で錐を写す。
規約：通常の錐の極限性はこの定義に不要。
使われ方：BF 1978 §2 の段ごとの極限条件の指定。 -/
def spectrumLevelCone (c : Cone F) (n : ℕ) : Cone (F ⋙ spectrumLevelFunctor n) :=
  (spectrumLevelFunctor n).mapCone c

/-- 概要：スペクトルの錐を指定段の点つき Hom の錐へ写す。
方針：指定段の Hom 関手で錐を写す。
規約：X と n を固定する。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の各段の Hom の普遍性。 -/
def spectrumStageHomCone (c : Cone F) (X : OmegaSpectrum.{u}) (n : ℕ) :
    Cone (F ⋙ spectrumStageHomFunctor X n) :=
  (spectrumStageHomFunctor X n).mapCone c

/-- 概要：指定段の錐が極限なら、その段の点つき Hom の錐も極限。
方針：点つき内部 Hom と基点の忘却の極限保存を使う。
規約：点つき写像空間の極限性を追加仮定にしない。
使われ方：HTT 4.2.4.1 のスペクトルの Hom の普遍射を各段で構成する。 -/
def spectrumStageHomCone_isLimit (c : Cone F) (X : OmegaSpectrum.{u}) (n : ℕ)
    (hc : IsLimit (spectrumLevelCone c n)) : IsLimit (spectrumStageHomCone c X n) := by
  change IsLimit ((pointedMappingFunctor (X.level n).space).mapCone
    ((spectrumLevelFunctor n).mapCone c))
  exact isLimitOfPreserves (pointedMappingFunctor (X.level n).space) hc

/-- 概要：スペクトルの Hom の図式上の錐を指定段の Hom の錐へ評価する。
方針：各段の評価の自然変換を図式で前合成し、元の錐へ後合成する。
規約：パラメータは元の錐 s の任意の単体集合 s.pt。
使われ方：BF 1978 §2、全 Hom パラメータの普遍性の入力。 -/
def spectrumHomParameterCone (X : OmegaSpectrum.{u}) (n : ℕ)
    (s : Cone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F X)) : Cone (F ⋙ spectrumStageHomFunctor X n) :=
  (Cone.postcompose (Functor.whiskerLeft F (spectrumMappingEvaluation X n))).obj s

/-- 概要：各段で極限となるスペクトルの錐へ、Hom パラメータの族を各段で持ち上げる。
方針：各段の Hom の錐の極限の普遍射を使う。
規約：元の錐 s は Hom 図式上の任意の錐。
使われ方：HTT 4.2.4.1 の実際の写像空間への普遍射の段ごとの構成。 -/
def spectrumHomLimitFamily (c : Cone F) (hc : ∀ n, IsLimit (spectrumLevelCone c n))
    (X : OmegaSpectrum.{u}) (s : Cone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F X)) (n : ℕ) :
    s.pt ⟶ (PointedObject.basedHom (X.level n).space (c.pt.level n).space).right :=
  (spectrumStageHomCone_isLimit c X n (hc n)).lift (spectrumHomParameterCone X n s)

/-- 概要：各段の普遍族を錐の脚で後合成すると元のパラメータの族のその段の評価になる。
方針：各段の Hom の極限の普遍射の射影則を使う。
規約：全ての添字 i と全ての段 n についての射の厳密な等式。
使われ方：BF 1978 §2、スペクトルの構造射との整合性と全 Hom の普遍性の検証。 -/
lemma spectrumHomLimitFamily_fac (c : Cone F) (hc : ∀ n, IsLimit (spectrumLevelCone c n))
    (X : OmegaSpectrum.{u}) (s : Cone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F X)) (n : ℕ) (i : I) :
    spectrumHomLimitFamily c hc X s n ≫
        (pointedMappingFunctor (X.level n).space).map ((c.π.app i).app n) =
      s.π.app i ≫ OmegaSpectrum.evaluation X (F.obj i) n :=
  (spectrumStageHomCone_isLimit c X n (hc n)).fac (spectrumHomParameterCone X n s) i

/-- 概要：各段の普遍族はスペクトルの構造射と整合する。
方針：次段の境界 Hom の極限の射影で検査し、前合成・後合成・懸垂の自然性を使う。
規約：全ての Hom パラメータを同時に扱う。
使われ方：BF 1978 §2、実際の全写像空間への普遍的な持ち上げの条件。 -/
lemma spectrumHomLimitFamily_condition (c : Cone F) (hc : ∀ n, IsLimit (spectrumLevelCone c n))
    (X : OmegaSpectrum.{u}) (s : Cone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F X)) (n : ℕ) :
    spectrumHomLimitFamily c hc X s (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (c.pt.level (n + 1)).space =
      spectrumHomLimitFamily c hc X s n ≫ OmegaSpectrum.mappingStep X c.pt n := by
  have hb := isLimitOfPreserves (pointedMappingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space))
    (hc (n + 1))
  apply hb.hom_ext
  intro i
  change (spectrumHomLimitFamily c hc X s (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (c.pt.level (n + 1)).space) ≫
      (pointedMappingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map ((c.π.app i).app (n + 1)) =
    (spectrumHomLimitFamily c hc X s n ≫ OmegaSpectrum.mappingStep X c.pt n) ≫
      (pointedMappingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map ((c.π.app i).app (n + 1))
  rw [Category.assoc, pointedMapping_pre_post, ← Category.assoc,
    spectrumHomLimitFamily_fac]
  rw [Category.assoc (spectrumHomLimitFamily c hc X s n)
    (OmegaSpectrum.mappingStep X c.pt n),
    spectrumMappingStep_post (Y := c.pt) (Z := F.obj i) X (c.π.app i) n,
    ← Category.assoc, spectrumHomLimitFamily_fac c hc X s n i]
  simp only [Category.assoc]
  rw [OmegaSpectrum.evaluation_condition]

/-- 概要：Hom 図式上の錐からスペクトルの実際の全写像空間への普遍射を作る。
方針：各段の普遍族を L9 の切断写像空間の普遍性で束ねる。
規約：写像空間の別模型や追加の比較同値は導入しない。
使われ方：HTT 4.2.4.1 の Sp の豊穣 Hom の極限の普遍性の構成。 -/
def spectrumHomConeLift (c : Cone F) (hc : ∀ n, IsLimit (spectrumLevelCone c n))
    (X : OmegaSpectrum.{u}) (s : Cone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F X)) :
    s.pt ⟶ OmegaSpectrum.mappingSpace X c.pt :=
  TruncatedMapping.familyLift (fun n ↦ (X.level n).space) (fun n ↦ (c.pt.level n).space)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) X.sigma (OmegaSpectrum.mappingStep X c.pt)
    (spectrumHomLimitFamily c hc X s) (spectrumHomLimitFamily_condition c hc X s)

/-- 概要：全写像空間への普遍射を各段で評価すると各段の普遍族になる。
方針：L9 の全切断への持ち上げの射影則を使う。
規約：全ての段と Hom パラメータに成立する。
使われ方：BF 1978 §2、豊穣 Hom の普遍射の射影則と一意性の検証。 -/
lemma spectrumHomConeLift_evaluation (c : Cone F) (hc : ∀ n, IsLimit (spectrumLevelCone c n))
    (X : OmegaSpectrum.{u}) (s : Cone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F X)) (n : ℕ) :
    spectrumHomConeLift c hc X s ≫ OmegaSpectrum.evaluation X c.pt n =
      spectrumHomLimitFamily c hc X s n :=
  TruncatedMapping.familyLift_evaluation _ _ _ _ _ _ _ n

/-- 概要：全写像空間への普遍射を錐の脚で後合成すると入力の Hom 錐の脚になる。
方針：各段の評価で検査し、後合成の自然性と各段の普遍射の射影則を使う。
規約：通常の零単体だけでなく全単体集合の射の等式。
使われ方：HTT 4.2.4.1 の実際の Hom 極限の射影則。 -/
lemma spectrumHomConeLift_fac (c : Cone F) (hc : ∀ n, IsLimit (spectrumLevelCone c n))
    (X : OmegaSpectrum.{u}) (s : Cone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F X)) (i : I) :
    spectrumHomConeLift c hc X s ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c X).π.app i = s.π.app i := by
  apply OmegaSpectrum.mapping_hom_ext
  intro n
  change (spectrumHomConeLift c hc X s ≫
    ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map
      (c.π.app i)) ≫ OmegaSpectrum.evaluation X (F.obj i) n = _
  rw [Category.assoc, spectrumHomMap_evaluation, ← Category.assoc,
    spectrumHomConeLift_evaluation]
  exact spectrumHomLimitFamily_fac c hc X s n i

/-- 概要：Hom 図式上の錐から全写像空間への射は射影との整合性で一意に決まる。
方針：各段の Hom の極限の一意性と L9 の全段評価の外延性を使う。
規約：Hom パラメータの単体集合は任意。
使われ方：BF 1978 §2、HTT 4.2.4.1 の豊穣 Hom の極限の一意性。 -/
lemma spectrumHomConeLift_uniq (c : Cone F) (hc : ∀ n, IsLimit (spectrumLevelCone c n))
    (X : OmegaSpectrum.{u}) (s : Cone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F X))
    (m : s.pt ⟶ OmegaSpectrum.mappingSpace X c.pt)
    (hm : ∀ i, m ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c X).π.app i = s.π.app i) :
    m = spectrumHomConeLift c hc X s := by
  apply OmegaSpectrum.mapping_hom_ext
  intro n
  rw [spectrumHomConeLift_evaluation]
  apply (spectrumStageHomCone_isLimit c X n (hc n)).hom_ext
  intro i
  change (m ≫ OmegaSpectrum.evaluation X c.pt n) ≫
      (pointedMappingFunctor (X.level n).space).map ((c.π.app i).app n) =
    spectrumHomLimitFamily c hc X s n ≫
      (pointedMappingFunctor (X.level n).space).map ((c.π.app i).app n)
  change (m ≫ OmegaSpectrum.evaluation X c.pt n) ≫
      (PointedObject.basedHomMap (X.level n).space ((c.π.app i).app n)).right =
    spectrumHomLimitFamily c hc X s n ≫
      (PointedObject.basedHomMap (X.level n).space ((c.π.app i).app n)).right
  have hm' : m ≫
      ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map
        (c.π.app i) = s.π.app i := hm i
  rw [Category.assoc, ← spectrumHomMap_evaluation (Y := c.pt) (Z := F.obj i) X (c.π.app i) n,
    ← Category.assoc, hm']
  exact (spectrumHomLimitFamily_fac c hc X s n i).symm

/-- 概要：L9 の Ω スペクトルの錐が各段で極限なら、実際の豊穣 Hom の錐も極限。
方針：全パラメータで構成した普遍射と射影則・一意性を束ねる。
規約：Hom 錐の極限性を追加仮定にしない。段ごとの極限対象の存在・Ω 条件は別途検証する。
使われ方：HTT 4.2.4.1、BF 1978 §2、Kerodon 7.5.4.6（Tag 03BB）、γ3c の Sp の極限への入力。 -/
def spectrumHomCone_isLimit_of_levelwise (c : Cone F)
    (hc : ∀ n, IsLimit (spectrumLevelCone c n)) (X : OmegaSpectrum.{u}) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c X) where
  lift s := spectrumHomConeLift c hc X s
  fac s i := spectrumHomConeLift_fac c hc X s i
  uniq s m hm := spectrumHomConeLift_uniq c hc X s m hm

end

end SerrePositivity.InfinityCategories.HomotopyLimits
