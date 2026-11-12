module

public import SerrePositivity.KST.Spectra.MappingPathSequence
public import SerrePositivity.KST.Spectra.CofibrantSequenceLifting
public import SerrePositivity.KST.Spectra.FiberOmegaSpectrum

/-!
概要：任意の Ω スペクトルの射を各段で Kan fibration となる射へ置換する。
方針：mapping path 列を単射置換し、cofibrant な元の源から厳密に持ち上げる。
規約：中間対象は本レーンの BF cofibrant–fibrant 対象。
使われ方：BF 1978 §2、Goerss–Jardine I §7、HTT A.3.3、HA §1.4.2。任意の射の fiber 列。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：射の mapping path の Kan Ω 列。
方針：Kan 列へ忘却して mapping path を構成する。
規約：単射条件を課す前の中間列。
使われ方：BF 1978 §2、Goerss–Jardine I §7。fibration 置換の入力。 -/
abbrev fibrationPath {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) : KanSequence.{u} :=
  KanSequence.mappingPathSequence (sequenceHom f)

/-- 概要：射の mapping path の中間列は Ω 条件を持つ。
方針：源への射影の全単射 RLP を通して元の源の Ω 条件を移す。
規約：厳密 Ω 同型は要求しない。
使われ方：BF 1978 §2、HA §1.4.2。cofibrant–fibrant 置換の Ω 条件。 -/
theorem fibrationPath_omegaCondition {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    (fibrationPath f).OmegaCondition :=
  KanSequence.mappingPathSequence_omegaCondition (sequenceHom f) X.toKanSequence_omega

/-- 概要：射の fibration 置換の中間 Ω スペクトル。
方針：mapping path の Kan Ω 列を単射置換する。
規約：構造射は単射であり、全ての段は Kan。
使われ方：BF 1978 §2、HTT A.3.3。任意の射の fiber の源。 -/
def fibrationReplacement {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) : OmegaSpectrum.{u} :=
  (fibrationPath f).cofibrantOmegaSpectrum (fibrationPath_omegaCondition f)

/-- 概要：単射置換した中間対象から元の mapping path 列への比較射。
方針：構成済みの単射置換の比較射を使う。
規約：全ての段で全単射への RLP を持つ。
使われ方：BF 1978 §2、HTT A.3.3。厳密な持ち上げの右辺。 -/
def fibrationReplacementComparison {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    KanSequence.Hom (fibrationReplacement f).toKanSequence (fibrationPath f) :=
  (fibrationPath f).cofibrantOmegaProjection (fibrationPath_omegaCondition f)

/-- 概要：fibration 置換の中間対象から元の標的への厳密な射。
方針：単射置換の比較射と mapping path の終点射を合成する。
規約：元の射の因子分解の右因子。
使われ方：BF 1978 §2、Goerss–Jardine I §7。任意の射の fiber 列。 -/
def fibrationReplacementProjection {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    (fibrationReplacement f) ⟶ Y where
  app n := ((fibrationReplacementComparison f).app n) ≫
    (KanSequence.mappingPathTarget (sequenceHom f)).app n
  comm := ((fibrationReplacementComparison f).comp
    (KanSequence.mappingPathTarget (sequenceHom f))).comm

/-- 概要：置換した右因子は各段で Kan fibration。
方針：単射置換の比較射の fibration と mapping path の終点射を合成する。
規約：元の射に fibration 性を仮定しない。
使われ方：BF 1978 §2、HTT A.3.3。任意の射の長完全列。 -/
instance fibrationReplacementProjection_fibration {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    ∀ n, Fibration ((fibrationReplacementProjection f).app n).right := by
  intro n
  let : Fibration ((fibrationReplacementComparison f).app n).right :=
    (SSet.modelCategoryQuillen.fibration_iff _).2 (fun _ _ j hj ↦
      (KanSequence.replacementStage (fibrationPath f) n).projection_rlp j (J_le_monomorphisms _ hj))
  change Fibration (((fibrationReplacementComparison f).app n).right ≫
    ((KanSequence.mappingPathTarget (sequenceHom f)).app n).right)
  infer_instance

/-- 概要：元の cofibrant な源から置換の中間 Kan 列への厳密な持ち上げ。
方針：元の構造射の単射性と置換比較射の全単射 RLP を使う。
規約：mapping path の定数 path の比較射を厳密に持ち上げる。
使われ方：BF 1978 §2、HTT A.3.3。元の射の因子分解の左因子。 -/
def fibrationReplacementLift {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    KanSequence.Hom X.toKanSequence (fibrationReplacement f).toKanSequence :=
  KanSequence.liftHom X.sigma_mono (fibrationReplacementComparison f)
    (fun n ↦ (KanSequence.replacementStage (fibrationPath f) n).projection_rlp)
    (KanSequence.mappingPathComparison (sequenceHom f))

/-- 概要：元の源から fibration 置換の中間 Ω スペクトルへの厳密な射。
方針：Kan 列の厳密な持ち上げを Ω スペクトルの射へ束ねる。
規約：元の射の因子分解の左因子。
使われ方：BF 1978 §2、HA §1.4.2。置換前後の整数次数群の比較。 -/
def fibrationReplacementUnit {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    X ⟶ (fibrationReplacement f) where
  app := (fibrationReplacementLift f).app
  comm := (fibrationReplacementLift f).comm

/-- 概要：持ち上げた比較射を単射置換の右射へ合成すると定数 path の比較射。
方針：cofibrant な源からの厳密持ち上げの計算式を使う。
規約：各段の点つき射の等式。
使われ方：BF 1978 §2、HTT A.3.3。厳密な因子分解と π_* 比較。 -/
theorem fibrationReplacementUnit_comparison {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    (fibrationReplacementUnit f).app n ≫ (fibrationReplacementComparison f).app n =
      (KanSequence.mappingPathComparison (sequenceHom f)).app n :=
  KanSequence.liftHom_fac X.sigma_mono _ _ _ n

/-- 概要：構成した二つの Ω スペクトルの射の合成は元の射。
方針：単射置換への持ち上げの比較式と定数 path の終点評価を使う。
規約：ホモトピーでなく通常の圏の等式。
使われ方：BF 1978 §2、HTT A.3.3。任意の射の厳密な fibration 置換。 -/
@[reassoc (attr := simp)]
theorem fibrationReplacement_fac {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    (fibrationReplacementUnit f) ≫ (fibrationReplacementProjection f) = f := by
  apply Hom.ext
  intro n
  change (fibrationReplacementUnit f).app n ≫ ((fibrationReplacementComparison f).app n ≫
    (KanSequence.mappingPathTarget (sequenceHom f)).app n) = f.app n
  rw [← Category.assoc, fibrationReplacementUnit_comparison]
  exact KanSequence.mappingPathComparison_target (sequenceHom f) n

/-- 概要：元の源から fibration 置換の中間対象への射は各段で全基点 π_* 同型。
方針：単射置換の比較射を後ろから打ち消し、mapping path の比較射の同型性を使う。
規約：零次数を含む。
使われ方：BF 1978 §2、Goerss–Jardine I §7。整数次数群の置換不変性。 -/
theorem fibrationReplacementUnit_levelwise {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((fibrationReplacementUnit f).app n).right := by
  have hq : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((fibrationReplacementComparison f).app n).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _
      (KanSequence.replacementStage (fibrationPath f) n).projection_rlp
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := ((fibrationReplacementComparison f).app n).right) _ hq
  rw [show ((fibrationReplacementUnit f).app n).right ≫
      ((fibrationReplacementComparison f).app n).right =
        ((KanSequence.mappingPathComparison (sequenceHom f)).app n).right from
    congrArg Under.Hom.right (fibrationReplacementUnit_comparison f n)]
  exact KanSequence.mappingPathComparison_piIsomorphism (sequenceHom f) n

/-- 概要：fibration 置換の左因子は全整数次数の π_* 同型。
方針：段ごとの全基点 π_* 同型を整数次数の誘導準同型へ移す。
規約：coherent nerve 内の同値との比較は γ3 後に扱う。
使われ方：BF 1978 §2、HA §1.4.2。任意の射の長完全列の移送。 -/
theorem fibrationReplacementUnit_piIsomorphism {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    PiIsomorphism (fibrationReplacementUnit f) :=
  piIsomorphism_of_levelwise _ (fibrationReplacementUnit_levelwise f)

/-- 概要：fibration 置換の中間 Ω スペクトルから元の源への厳密な射。
方針：単射置換の比較射と mapping path の源射影を合成する。
規約：元の源の比較射の厳密な左逆。
使われ方：BF 1978 §2、HA §1.4.2。任意の射の fiber の包含。 -/
def fibrationReplacementRetraction {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    fibrationReplacement f ⟶ X where
  app n := (fibrationReplacementComparison f).app n ≫
    (KanSequence.mappingPathSource (sequenceHom f)).app n
  comm := ((fibrationReplacementComparison f).comp
    (KanSequence.mappingPathSource (sequenceHom f))).comm

/-- 概要：元の源の比較射と源への射影の合成は恒等射。
方針：厳密な持ち上げの比較式と定数 path の源射影を計算する。
規約：Ω スペクトルの圏の等式。
使われ方：BF 1978 §2、HTT A.3.3。fiber の元の源への包含。 -/
@[reassoc (attr := simp)]
theorem fibrationReplacementUnit_retraction {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    fibrationReplacementUnit f ≫ fibrationReplacementRetraction f = 𝟙 X := by
  apply Hom.ext
  intro n
  change (fibrationReplacementUnit f).app n ≫ ((fibrationReplacementComparison f).app n ≫
    (KanSequence.mappingPathSource (sequenceHom f)).app n) = 𝟙 _
  rw [← Category.assoc, fibrationReplacementUnit_comparison]
  exact KanSequence.mappingPathComparison_source (sequenceHom f) n

/-- 概要：源への射影の誘導準同型は比較射の誘導準同型の左逆。
方針：スペクトルの厳密な合成恒等式をホモトピー群へ送る。
規約：全整数次数で有効。
使われ方：BF 1978 §2、HA §1.4.2。長完全列の移送の可換式。 -/
@[simp]
theorem fibrationReplacementRetraction_unit {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (j : ℤ) (a : homotopyGroup X j) :
    homotopyMap (fibrationReplacementRetraction f) j
      (homotopyMap (fibrationReplacementUnit f) j a) = a := by
  have h := congrArg (fun t : X ⟶ X ↦ homotopyMap t j)
    (fibrationReplacementUnit_retraction f)
  rw [homotopyMap_comp, homotopyMap_id] at h
  exact DFunLike.congr_fun h a

/-- 概要：源への射影の誘導準同型は比較射の誘導準同型の右逆でもある。
方針：比較射の全射性で元を表示し、左逆の計算式を使う。
規約：スペクトルの射そのものの右逆性は主張しない。
使われ方：BF 1978 §2、HA §1.4.2。長完全列の元の源への移送。 -/
@[simp]
theorem fibrationReplacementUnit_retraction_map {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (j : ℤ) (b : homotopyGroup (fibrationReplacement f) j) :
    homotopyMap (fibrationReplacementUnit f) j
      (homotopyMap (fibrationReplacementRetraction f) j b) = b := by
  obtain ⟨a, rfl⟩ := (fibrationReplacementUnit_piIsomorphism f j).surjective b
  rw [fibrationReplacementRetraction_unit]

/-- 概要：置換の比較同型は元の射の誘導準同型と右因子の誘導準同型を対応させる。
方針：厳密な因子分解をホモトピー群へ送る。
規約：全整数次数。
使われ方：BF 1978 §2、HA §1.4.2。長完全列の底の位置の移送。 -/
theorem fibrationReplacement_projection_map {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (j : ℤ) (a : homotopyGroup X j) :
    homotopyMap (fibrationReplacementProjection f) j
      (homotopyMap (fibrationReplacementUnit f) j a) = homotopyMap f j a := by
  have h := congrArg (fun t : X ⟶ Y ↦ homotopyMap t j) (fibrationReplacement_fac f)
  rw [homotopyMap_comp] at h
  exact DFunLike.congr_fun h a

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
