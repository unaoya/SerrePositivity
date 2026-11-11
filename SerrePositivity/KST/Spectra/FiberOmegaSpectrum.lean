module

public import SerrePositivity.KST.Spectra.FiberKanSequence
public import SerrePositivity.KST.Spectra.CofibrantOmegaSequence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationComparison
public import SerrePositivity.KST.Spectra.PostMappingFibration
public import SerrePositivity.KST.Spectra.LoopFiber

/-!
概要：段ごとの Kan fibration の fiber 列の Ω 条件と BF の Ω スペクトルへの置換。
方針：loop が fiber を保存する厳密同型と全基点の fiber 比較定理で随伴構造射を検証する。
規約：ここでは各段が Kan fibration の射を扱う。∞ 極限の普遍性は主張しない。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2、HA §1.4.2。スペクトルの fiber 列。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.KanSequence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Ω 条件を持つ二列の段ごとの Kan fibration の fiber 列も Ω 条件を持つ。
方針：fiber の随伴構造射を loop–fiber 同型へ合成し、全空間・底の Ω 条件から比較する。
規約：全基点・零次数を含む π_* 同型を証明する。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2、HA §1.4.2。fiber の Ω 条件。 -/
theorem Hom.fiber_omegaCondition {X Y : KanSequence.{u}} (p : Hom X Y)
    (hp : ∀ n, Fibration (p.app n).right) (hX : X.OmegaCondition) (hY : Y.OmegaCondition) :
    (p.fiber hp).OmegaCondition := by
  intro n
  let : Fibration (p.app n).right := hp n
  let : Fibration (p.app (n + 1)).right := hp (n + 1)
  let pp := PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (p.app (n + 1))
  let : Fibration pp.right := PointedMapping.post_fibration _ _
  let aX := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level n).space (X.level (n + 1)).space) (X.sigma n)
  let aY := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (Y.level n).space (Y.level (n + 1)).space) (Y.sigma n)
  let a : pointedFiber (p.app n) ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (pointedFiber (p.app (n + 1))) :=
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _) (p.fiberSigma n)
  let i := loopPointedFiberIso (p.app (n + 1))
  let φ := a ≫ i.hom
  have hφ : φ ≫ pointedFiberι pp = pointedFiberι (p.app n) ≫ aX := by
    dsimp only [φ, i, pp]
    rw [Category.assoc, loopPointedFiberIso_hom_ι]
    exact ((p.fiberInclusion hp).adjoint_comm n).symm
  have hc : (p.app n).right ≫ aY.right = aX.right ≫ pp.right :=
    congrArg Under.Hom.right (p.adjoint_comm n)
  have hb : pp.right.app _ (aX.right.app _ (X.level n).space.basepoint) =
      pp.right.app _ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X.level (n + 1)).space).basepoint :=
    congrArg (pp.right.app _) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint aX)
  have hφπ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism φ.right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberMapOver_piIsomorphism (p.app n).right pp.right
      aX.right aY.right hc (hX n) (hY n) (X.level n).space.basepoint
      ((p.app n).right.app _ (X.level n).space.basepoint) rfl
      (pp.right.app _ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X.level (n + 1)).space).basepoint) hb φ.right
      (congrArg Under.Hom.right hφ)
  have hi : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism i.hom.right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso
      (X := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (pointedFiber (p.app (n + 1)))).right)
      (Y := (pointedFiber pp).right) (PointedSimplicialSet.forget.mapIso i)
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right
  exact (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (a.right ≫ i.hom.right) from hφπ).of_comp hi

/-- 概要：段ごとの Kan fibration の fiber 列を BF の Ω スペクトルへ置換する。
方針：fiber の Ω 条件を検証してから、単射な構造射を持つ列へ置換する。
規約：各段の fiber 自体が cofibrant であるとは仮定しない。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。Sp の対象としての fiber。 -/
def Hom.fiberOmegaSpectrum {X Y : KanSequence.{u}} (p : Hom X Y)
    (hp : ∀ n, Fibration (p.app n).right) (hX : X.OmegaCondition) (hY : Y.OmegaCondition) :
    OmegaSpectrum.{u} :=
  (p.fiber hp).cofibrantOmegaSpectrum (p.fiber_omegaCondition hp hX hY)

end

end SerrePositivity.KST.Spectra.KanSequence

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Ω スペクトルの射を Kan 列の厳密射として扱う。
方針：同じ各段の射と可換条件を使う。
規約：データを変えない忘却。
使われ方：BF 1978 §2。fiber 列の構成への入力。 -/
def sequenceHom {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y) :
    KanSequence.Hom X.toKanSequence Y.toKanSequence := ⟨p.app, p.comm⟩

/-- 概要：各段が Kan fibration の Ω スペクトルの射の fiber。
方針：各段の fiber に Ω 条件を証明し、構造射を単射へ置換する。
規約：Sp の ∞ 極限の主張は含めない。
使われ方：BF 1978 §2、HA §1.4.2。整数次数の長完全列の fiber 対象。 -/
def fiber {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y) (hp : ∀ n, Fibration (p.app n).right) :
    OmegaSpectrum.{u} :=
  (sequenceHom p).fiberOmegaSpectrum hp X.toKanSequence_omega Y.toKanSequence_omega

/-- 概要：置換した fiber の指定段から実際の点つき fiber への比較射。
方針：cofibrant な Kan 列への置換の段の比較射を使う。
規約：各段で全基点 π_* 同型。
使われ方：BF 1978 §2。長完全列を段ごとに計算する界面。 -/
def fiberLevelProjection {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
    (hp : ∀ n, Fibration (p.app n).right) (n : ℕ) :
    ((fiber p hp).level n).space ⟶ pointedFiber (p.app n) :=
  (KanSequence.replacementProjection ((sequenceHom p).fiber hp)).app n

/-- 概要：fiber の各段の比較射は全基点 π_* 同型。
方針：逐次的な境界 cell 分解による置換の比較定理を使う。
規約：各段の Kan 性を明示して使う。
使われ方：Goerss–Jardine I §7、BF 1978 §2。fiber の整数次数の完全性。 -/
theorem fiberLevelProjection_piIsomorphism {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
    (hp : ∀ n, Fibration (p.app n).right) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (fiberLevelProjection p hp n).right := by
  let : Fibration (p.app n).right := hp n
  exact KanSequence.replacementProjection_piIsomorphism ((sequenceHom p).fiber hp) n

/-- 概要：置換した fiber から全空間への厳密なスペクトルの射。
方針：置換の比較射と各段の fiber 包含を合成する。
規約：単射性を満たす BF 対象からの射。
使われ方：BF 1978 §2、HA §1.4.2。fiber 列の最初の射。 -/
def fiberInclusion {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
    (hp : ∀ n, Fibration (p.app n).right) : fiber p hp ⟶ X := by
  let F := (sequenceHom p).fiber hp
  let hF := (sequenceHom p).fiber_omegaCondition hp X.toKanSequence_omega Y.toKanSequence_omega
  let q := KanSequence.cofibrantOmegaProjection F hF
  let i := (sequenceHom p).fiberInclusion hp
  let qi := q.comp i
  exact ⟨qi.app, qi.comm⟩

/-- 概要：fiber 包含の各段は置換の比較射と実際の fiber 包含の合成。
方針：列の射の合成の定義を読む。
規約：点つき射の厳密な等式。
使われ方：BF 1978 §2。整数次数完全列と実際の fiber 列の接続。 -/
theorem fiberInclusion_app {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
    (hp : ∀ n, Fibration (p.app n).right) (n : ℕ) :
    (fiberInclusion p hp).app n = fiberLevelProjection p hp n ≫ pointedFiberι (p.app n) := rfl

/-- 概要：fiber 包含と元のスペクトルの射の合成は各段で零。
方針：実際の fiber 包含の零合成を置換の比較射へ前合成する。
規約：各段の点つき圏の零射として述べる。
使われ方：Goerss–Jardine I §7、BF 1978 §2。長完全列の零合成。 -/
@[simp]
theorem fiberInclusion_comp_app {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)
    (hp : ∀ n, Fibration (p.app n).right) (n : ℕ) :
    (fiberInclusion p hp).app n ≫ p.app n = 0 := by
  rw [fiberInclusion_app, Category.assoc, pointedFiberι_comp, comp_zero]

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
