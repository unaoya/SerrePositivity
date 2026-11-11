module
public import SerrePositivity.KST.NonConnective.SequentialCandidateMap

/-!
概要：元の逐次比較を受ける実候補比較の、同じ実余極限の脚と整数 π の作用。
方針：同じ射影下の厳密比較で hSp の可換性を証明し、Sp 正本の群比較へ写す。
規約：実懸垂列の比較・入力作用の自然性や Morita 不変性自体は主張しない。
使われ方：K-7 の実列比較が供給された場合の、非連結化候補の不変性の形式部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance candidateMapPiSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance candidateMapPiHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 概要：元の恒等逐次比較の実候補比較は全整数 π 上で恒等。
方針：同じ比較の hSp 恒等則を元の BF 群へ移す。
規約：代表 BF 射の厳密恒等は主張しない。
使われ方：元の候補群の関手性。 -/
theorem sequentialCandidateMap_pi_id (D : SpectrumSequence.{u}) (j : ℤ) :
    OmegaSpectrum.homotopyMap (sequentialCandidateMap (𝟙 D)) j = MonoidHom.id _ := by
  have he : SpectrumHo.hom (sequentialCandidateMap (𝟙 D)) =
      SpectrumHo.hom (𝟙 (sequentialSpectrum D)) := by
    rw [sequentialCandidateMap_hom, sequentialCandidateHoMap_id, SpectrumHo.hom_id]
  exact (SpectrumHo.homotopyMap_eq_of_hom_eq _ _ he j).trans
    (OmegaSpectrum.homotopyMap_id _ j)

/-- 概要：元の逐次比較の合成は同じ実候補比較の整数 π 作用の合成。
方針：hSp の同じ合成則を元の BF 群作用へ移す。
規約：同じ実比較の代表を保持する。
使われ方：元の候補群の関手性。 -/
theorem sequentialCandidateMap_pi_comp {D E F : SpectrumSequence.{u}}
    (η : D ⟶ E) (θ : E ⟶ F) (j : ℤ) :
    OmegaSpectrum.homotopyMap (sequentialCandidateMap (η ≫ θ)) j =
      (OmegaSpectrum.homotopyMap (sequentialCandidateMap θ) j).comp
        (OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j) := by
  have he : SpectrumHo.hom (sequentialCandidateMap (η ≫ θ)) =
      SpectrumHo.hom (sequentialCandidateMap η ≫ sequentialCandidateMap θ) := by
    rw [sequentialCandidateMap_hom, sequentialCandidateHoMap_comp, SpectrumHo.hom_comp,
      sequentialCandidateMap_hom, sequentialCandidateMap_hom]
  exact (SpectrumHo.homotopyMap_eq_of_hom_eq _ _ he j).trans
    (OmegaSpectrum.homotopyMap_comp _ _ j)

/-- 概要：同じ実非連結化候補の任意整数 π 群は厳密逐次比較に関手的。
方針：元の BF 比較の全整数 π の恒等・合成則を使う。
規約：逐次列を始域とし、未供給の dg 入力作用の自然性は主張しない。
使われ方：実懸垂列比較が供給された後の群比較の形式部分。 -/
def sequentialCandidatePiFunctor (j : ℤ) : SpectrumSequence.{u} ⥤ CommGrpCat.{u} where
  obj D := CommGrpCat.of (OmegaSpectrum.homotopyGroup (sequentialSpectrum D) j)
  map η := CommGrpCat.ofHom (OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j)
  map_id D := congrArg CommGrpCat.ofHom (sequentialCandidateMap_pi_id D j)
  map_comp η θ := congrArg CommGrpCat.ofHom (sequentialCandidateMap_pi_comp η θ j)

/-- 概要：同じ実候補比較は元の実余極限の脚と hSp で可換。
方針：同じ可逆射影を合成して、元の段別余極限の実比較式へ戻す。
規約：元の実余錐の脚の類を保持する。
使われ方：非連結化候補比較の群作用を元の入力段から読む。 -/
theorem sequentialCandidateMap_leg {D E : SpectrumSequence.{u}} (η : D ⟶ E)
    (a : SequentialIndex.{u}) :
    Truncated.HomotopyCategory.homMk (sequentialCandidateColimitLeg D a).toTruncated ≫
        SpectrumHo.hom (sequentialCandidateMap η) =
      SpectrumHo.hom (η.app a) ≫
        Truncated.HomotopyCategory.homMk (sequentialCandidateColimitLeg E a).toTruncated := by
  rw [sequentialCandidateColimitLeg_hom_eq, sequentialCandidateColimitLeg_hom_eq]
  change SpectrumHo.hom (OmegaSpectrum.filteredSpectrumInjection D a) ≫
    SpectrumHo.hom (sequentialCandidateMap η) =
      SpectrumHo.hom (η.app a) ≫ SpectrumHo.hom (OmegaSpectrum.filteredSpectrumInjection E a)
  have hp : IsIso (SpectrumHo.hom (sequentialReplacementProjection E)) :=
    OmegaSpectrum.isInvertible_of_piIsomorphism _ (sequentialReplacementProjection_piIsomorphism E)
  apply (cancel_mono (SpectrumHo.hom (sequentialReplacementProjection E))).mp
  rw [Category.assoc, sequentialCandidateMap_projection, ← Category.assoc,
    ← SpectrumHo.hom_comp, sequentialInjection_projection, ← SpectrumHo.hom_comp,
    sequentialLevelColimitMap_fac, SpectrumHo.hom_comp, Category.assoc,
    ← SpectrumHo.hom_comp (OmegaSpectrum.filteredSpectrumInjection E a)
      (sequentialReplacementProjection E), sequentialInjection_projection]

/-- 概要：同じ候補比較の整数 π 作用は元の各段からの実注入と可換。
方針：元の実余錐の脚の hSp 可換性を同じ BF 射の整数 π に移す。
規約：別の群余極限比較や注入へ取り替えない。
使われ方：K-7 の任意整数の末尾表示と供給された列比較の照合。 -/
theorem sequentialCandidateMap_pi_injection {D E : SpectrumSequence.{u}} (η : D ⟶ E)
    (a : SequentialIndex.{u}) (j : ℤ) :
    (OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j).comp
        (OmegaSpectrum.homotopyMap (OmegaSpectrum.filteredSpectrumInjection D a) j) =
      (OmegaSpectrum.homotopyMap (OmegaSpectrum.filteredSpectrumInjection E a) j).comp
        (OmegaSpectrum.homotopyMap (η.app a) j) := by
  have he := sequentialCandidateMap_leg η a
  rw [sequentialCandidateColimitLeg_hom_eq, sequentialCandidateColimitLeg_hom_eq] at he
  change SpectrumHo.hom (OmegaSpectrum.filteredSpectrumInjection D a) ≫
    SpectrumHo.hom (sequentialCandidateMap η) =
      SpectrumHo.hom (η.app a) ≫ SpectrumHo.hom (OmegaSpectrum.filteredSpectrumInjection E a) at he
  rw [← SpectrumHo.hom_comp, ← SpectrumHo.hom_comp] at he
  exact (OmegaSpectrum.homotopyMap_comp _ _ j).symm.trans
    ((SpectrumHo.homotopyMap_eq_of_hom_eq _ _ he j).trans
      (OmegaSpectrum.homotopyMap_comp _ _ j))

/-- 概要：各固定段から同じ実候補への元の整数 π 注入は、実逐次比較に自然。
方針：同じ実余極限の脚の群作用の可換性を自然変換へ束ねる。
規約：元の注入を保持し、dg 入力上の自然性はここから推論しない。
使われ方：K-7 の実懸垂列比較を、同じ連結比較・末尾表示へ接続する形式部分。 -/
def sequentialCandidatePiInjection (a : SequentialIndex.{u}) (j : ℤ) :
    (evaluation SequentialIndex.{u} OmegaSpectrum.{u}).obj a ⋙ OmegaSpectrum.homotopyFunctor j ⟶
      sequentialCandidatePiFunctor j where
  app D := CommGrpCat.ofHom
    (OmegaSpectrum.homotopyMap (OmegaSpectrum.filteredSpectrumInjection D a) j)
  naturality D E η := by
    exact congrArg CommGrpCat.ofHom (sequentialCandidateMap_pi_injection η a j).symm

/-- 概要：各段で全整数 π 同型な実逐次比較は、同じ実候補比較でも全整数 π 同型。
方針：同じ段別余極限比較の同型性と元の射影同型を、Sp 正本の BF 群比較へ渡す。
規約：実逐次比較 η の供給に条件付きであり、dg Morita 比較の存在は主張しない。
使われ方：K-7 e の実 Morita 列比較が供給された後の候補不変性。 -/
theorem sequentialCandidateMap_piIsomorphism {D E : SpectrumSequence.{u}} (η : D ⟶ E)
    (hη : ∀ a, OmegaSpectrum.PiIsomorphism (η.app a)) :
    OmegaSpectrum.PiIsomorphism (sequentialCandidateMap η) := by
  have hl : IsIso (SpectrumHo.hom (sequentialLevelColimitMap η)) :=
    OmegaSpectrum.isInvertible_of_piIsomorphism _ (sequentialLevelColimitMap_piIsomorphism η hη)
  have hm : IsIso (sequentialCandidateHoMap η) := by
    unfold sequentialCandidateHoMap
    infer_instance
  have hf : IsIso (SpectrumHo.hom (sequentialCandidateMap η)) := by
    rw [sequentialCandidateMap_hom]
    exact hm
  intro j
  have hb : IsIso (SpectrumHo.bfPiMap (SpectrumHo.hom (sequentialCandidateMap η)) j) := by
    unfold SpectrumHo.bfPiMap
    infer_instance
  rw [SpectrumHo.bfPiMap_hom] at hb
  exact ConcreteCategory.bijective_of_isIso
    (CommGrpCat.ofHom (OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j))

/-- 概要：同じ各段 π 同型の実逐次比較は、元の実候補間の可逆な Sp 辺を与える。
方針：同じ候補比較の整数 π 同型性を Sp 正本の検出定理へ渡す。
規約：元の BF 比較の辺を保ち、新しい比較同値を仮定しない。
使われ方：K-7 e の実列比較に条件付きの非連結化候補の可逆性。 -/
theorem sequentialCandidateMap_isInvertible {D E : SpectrumSequence.{u}} (η : D ⟶ E)
    (hη : ∀ a, OmegaSpectrum.PiIsomorphism (η.app a)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (sequentialCandidateMap η)) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _ (sequentialCandidateMap_piIsomorphism η hη)

end SerrePositivity.KST.NonConnective
