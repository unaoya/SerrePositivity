module

public import SerrePositivity.KST.Spectra.MappingPathSequence
public import SerrePositivity.KST.Spectra.FiberOmegaSpectrum
public import SerrePositivity.KST.Spectra.CofibrantSequenceLifting
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses
public import SerrePositivity.KST.Spectra.PointedComponentCancellation
public import SerrePositivity.KST.Spectra.SpectrumHomotopyEquivalences

/-!
概要：BF 対象間の各段の π_* 同型に対する逆向きの厳密なスペクトルの射。
方針：mapping path の acyclic な終点射へ cofibrant な列から厳密に切断を持ち上げる。
規約：∞ 圏の同値の反映は主張しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。符号を調整した loop 模型から元の模型へ戻る比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
  (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app n).right)

include hf

/-- 概要：段ごとの π_* 同型の mapping path の終点射は全ての単射へ RLP を持つ。
方針：各段の点つき mapping path の acyclic fibration の充填を使う。
規約：全基点と零次数の同型性を仮定する。
使われ方：BF 1978 §2、HTT A.3.3。逆方向の列の射の厳密な切断の存在。 -/
theorem inversePathTarget_rlp (n : ℕ) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      ((KanSequence.mappingPathTarget (sequenceHom f)).app n).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mappingPathProjection_rlp_of_piIsomorphism (f.app n) (hf n)

/-- 概要：mapping path の終点射へ標的の恒等射を列として厳密に持ち上げる。
方針：標的 Y の構造射の単射性と各段の全単射 RLP を使う。
規約：中間列の cofibrant 性は不要。
使われ方：BF 1978 §2。各段の独立な逆射でなく厳密な列の射を作る。 -/
def inversePathSection : KanSequence.Hom Y.toKanSequence
    (KanSequence.mappingPathSequence (sequenceHom f)) :=
  KanSequence.liftHom (X := Y.toKanSequence)
    (W := KanSequence.mappingPathSequence (sequenceHom f)) (Z := Y.toKanSequence)
    Y.sigma_mono (KanSequence.mappingPathTarget (sequenceHom f)) (inversePathTarget_rlp f hf)
    { app n := 𝟙 _, comm n := by simp }

/-- 概要：厳密な切断と終点射の合成は各段で恒等射。
方針：列の持ち上げの可換式を取り出す。
規約：ホモトピーでなく射の厳密な等式。
使われ方：BF 1978 §2。切断の π_* 同型性の検査。 -/
@[reassoc (attr := simp)]
theorem inversePathSection_target (n : ℕ) :
    (inversePathSection f hf).app n ≫
      (KanSequence.mappingPathTarget (sequenceHom f)).app n = 𝟙 _ :=
  KanSequence.liftHom_fac (X := Y.toKanSequence)
    (W := KanSequence.mappingPathSequence (sequenceHom f)) (Z := Y.toKanSequence)
    Y.sigma_mono (KanSequence.mappingPathTarget (sequenceHom f)) (inversePathTarget_rlp f hf)
    { app n := 𝟙 _, comm n := by simp } n

/-- 概要：各段で π_* 同型の BF 射に対する逆方向の厳密な射。
方針：mapping path の切断に元の源への射影を合成する。
規約：逆写像の選択に厳密な自然性は要求しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。loop 模型の比較射の向きを戻す。 -/
def levelwiseInverse : Y ⟶ X := by
  let g := (inversePathSection f hf).comp (KanSequence.mappingPathSource (sequenceHom f))
  exact { app := g.app, comm := g.comm }

/-- 概要：選んだ逆方向の厳密射も各段で全基点 π_* 同型。
方針：切断の終点射との合成を打ち消し、源射影の同型性を合成する。
規約：零次数を含む。
使われ方：Goerss–Jardine I §7、BF 1978 §2。比較の逆方向の同型性。 -/
theorem levelwiseInverse_levelwise (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((levelwiseInverse f hf).app n).right := by
  have hq := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (inversePathTarget_rlp f hf n)
  have hs : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((inversePathSection f hf).app n).right := by
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp
      (g := ((KanSequence.mappingPathTarget (sequenceHom f)).app n).right) _ hq
    have h := congrArg Under.Hom.right (inversePathSection_target f hf n)
    change ((inversePathSection f hf).app n).right ≫
      ((KanSequence.mappingPathTarget (sequenceHom f)).app n).right = 𝟙 _ at h
    rw [h]
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id _
  exact hs.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _
    (KanSequence.mappingPathSource_rlp (sequenceHom f) n))

/-- 概要：選んだ逆方向の射は各段で左ホモトピー逆となる。
方針：mapping path の終点射に対する二つの同じ合成を垂直ホモトピーで比較する。
規約：主張は各段の点つき射の成分での等式。
使われ方：Goerss–Jardine I §7、BF 1978 §2。逆方向の射が元の群準同型の逆を与える検査。 -/
theorem levelwiseInverse_left_component (n : ℕ) :
    PointedMapping.componentOf (f.app n ≫ (levelwiseInverse f hf).app n) =
      PointedMapping.componentOf (𝟙 (X.level n).space) := by
  let u := (KanSequence.mappingPathComparison (sequenceHom f)).app n
  let r := (KanSequence.mappingPathSource (sequenceHom f)).app n
  let p := (KanSequence.mappingPathTarget (sequenceHom f)).app n
  let s := (inversePathSection f hf).app n
  let fn : (X.toKanSequence.level n).space ⟶ (Y.toKanSequence.level n).space := f.app n
  change PointedMapping.componentOf (fn ≫ (s ≫ r)) =
    PointedMapping.componentOf (𝟙 (X.toKanSequence.level n).space)
  have hup : u ≫ p = fn := KanSequence.mappingPathComparison_target (sequenceHom f) n
  have hur : u ≫ r = 𝟙 _ := KanSequence.mappingPathComparison_source (sequenceHom f) n
  have hsp : s ≫ p = 𝟙 _ := inversePathSection_target f hf n
  have h : u ≫ p = (fn ≫ s) ≫ p := by
    rw [Category.assoc, hsp, Category.comp_id, hup]
  have hc := PointedMapping.componentOf_eq_of_comp_eq_rlp p
    (inversePathTarget_rlp f hf n) u (fn ≫ s) h
  have hpost := PointedMapping.componentOf_comp_right hc r
  rw [← Category.assoc, ← hpost, hur]

/-- 概要：選んだ逆方向の射は各段で右ホモトピー逆となる。
方針：mapping path の源射影へ同じ合成を持つ切断を比較し、終点射を後合成する。
規約：スペクトル全体の enriched ホモトピーは主張しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。成分上で両向きの逆となる比較射。 -/
theorem levelwiseInverse_right_component (n : ℕ) :
    PointedMapping.componentOf ((levelwiseInverse f hf).app n ≫ f.app n) =
      PointedMapping.componentOf (𝟙 (Y.level n).space) := by
  let u := (KanSequence.mappingPathComparison (sequenceHom f)).app n
  let r := (KanSequence.mappingPathSource (sequenceHom f)).app n
  let p := (KanSequence.mappingPathTarget (sequenceHom f)).app n
  let s := (inversePathSection f hf).app n
  let fn : (X.toKanSequence.level n).space ⟶ (Y.toKanSequence.level n).space := f.app n
  change PointedMapping.componentOf ((s ≫ r) ≫ fn) =
    PointedMapping.componentOf (𝟙 (Y.toKanSequence.level n).space)
  have hup : u ≫ p = fn := KanSequence.mappingPathComparison_target (sequenceHom f) n
  have hur : u ≫ r = 𝟙 _ := KanSequence.mappingPathComparison_source (sequenceHom f) n
  have hsp : s ≫ p = 𝟙 _ := inversePathSection_target f hf n
  have h : s ≫ r = ((s ≫ r) ≫ u) ≫ r := by
    simp only [Category.assoc, hur, Category.comp_id]
  have hc := PointedMapping.componentOf_eq_of_comp_eq_rlp r
    (KanSequence.mappingPathSource_rlp (sequenceHom f) n) s ((s ≫ r) ≫ u) h
  have hpost := PointedMapping.componentOf_comp_right hc p
  simpa only [Category.assoc, hup, hsp] using hpost.symm

/-- 概要：選んだ逆方向の BF 射は全整数次数で π_* 同型。
方針：各段の全基点 π_* 同型性を任意段表示で整数次数へ移す。
規約：coherent nerve の同値との比較は主張しない。
使われ方：BF 1978 §2、HA §1.4.2。符号を調整した loop 模型から有理化の模型へ戻す。 -/
theorem levelwiseInverse_piIsomorphism : PiIsomorphism (levelwiseInverse f hf) :=
  piIsomorphism_of_levelwise _ (levelwiseInverse_levelwise f hf)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
