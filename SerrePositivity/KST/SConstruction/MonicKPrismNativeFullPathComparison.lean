module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeDiskPaths

/-! # 元の全 raw trace を持つ二円柱の端点固定実比較
概要：元の次段補正列から共通末尾を実回収し、比較複体の両辺路全体を実比較する。
方針：全射影 trace の先頭を実辺路へ照合して切断し、元の三角形と全交換列を使う。
規約：元の全区間・全末尾を保持し、比較や末尾の存在を入力にしない。
使われ方：元の前段構造射の像と次段射影の全実比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の射影補正全列から切り出した、同じ実共有末尾。 -/
def monicKPrismNativeSharedTail (n : ℕ) :=
  familyChainPrefixTail (monicKPrismNativeProjectedCorrectionChain F f g n)
    (monicKPrismNativeDiskProjectedPath F f g n)
    (by rw [monicKPrismNativeProjectedCorrectionChain_trace]; exact List.take_left)
    (monicKPrismNativeDiskProjectedPath_trace_ne_nil F f g n)

/-- 切り出した末尾は、元の後半全区間の同じ構造射の像そのもの。 -/
lemma monicKPrismNativeSharedTail_trace (n : ℕ) :
    familyHomotopyChainTrace (monicKPrismNativeSharedTail F f g n) =
      (monicKPrismCompositeSecondTrace F f g n).map (fun h =>
        (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ h ≫
          RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) := by
  rw [monicKPrismNativeSharedTail, familyChainPrefixTail_trace,
    monicKPrismNativeProjectedCorrectionChain_trace, List.drop_left]

/-- 元の合成面・一境界・実回収した共通末尾の全列。 -/
def monicKPrismNativeFullDirectPath (n : ℕ) :=
  familyTriangleStripDirect
    (familyTriangleDirect (monicKPrismCompositionNativeTriangle n F f g))
    (monicKPrismNativeSecondCompatibilityTransport F f g n) (monicKPrismNativeSharedTail F f g n)

/-- 元の第一面・零境界・出口・実回収した共通末尾の全列。 -/
def monicKPrismNativeFullProjectedPath (n : ℕ) :=
  familyTriangleStripProjected
    (familyTriangleFirst (monicKPrismCompositionNativeTriangle n F f g))
    (monicKPrismNativeSecondCompatibilityTransport F f g n) (monicKPrismNativeSharedTail F f g n)

/-- 射影側の全列は元の次段射影の全区間を同じ順序で持つ。 -/
lemma monicKPrismNativeFullProjectedPath_trace (n : ℕ) :
    familyHomotopyChainTrace (monicKPrismNativeFullProjectedPath F f g n) =
      familyHomotopyChainTrace (monicKPrismNativeProjectedCorrectionChain F f g n) := by
  rw [monicKPrismNativeFullProjectedPath, familyTriangleStripProjected_trace,
    monicKPrismNativeProjectedCorrectionChain_trace, monicKPrismNativeDiskProjectedPath,
    familyTriangleStripProjected_trace]
  simp only [familyHomotopyChainTrace, List.cons_append, List.append_assoc,
    monicKPrismNativeSharedTail_trace]
  rfl

/-- 他側の全列は、元の合成適合円柱と前段の全補正の構造射の像。 -/
lemma monicKPrismNativeFullDirectPath_trace (n : ℕ) :
    familyHomotopyChainTrace (monicKPrismNativeFullDirectPath F f g n) =
      ((nerveMap (compositionStringComposite f g) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismRawSequenceCompatibility n F (f ≫ g)).h) ::
      (familyHomotopyChainTrace (monicKPrismNativeCompositeCorrectionChain F f g n)).map
        (· ≫ RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) := by
  have he : familyHomotopyChainTrace (monicKPrismNativeFullDirectPath F f g n) =
      familyHomotopyChainTrace (monicKPrismNativeDiskDirectPath F f g n) ++
        familyHomotopyChainTrace (monicKPrismNativeSharedTail F f g n) := by
    rw [monicKPrismNativeFullDirectPath, monicKPrismNativeDiskDirectPath,
      familyTriangleStripDirect_trace, familyTriangleStripDirect_trace]
    simp only [familyHomotopyChainTrace, List.append_nil, List.cons_append]
  rw [he, monicKPrismNativeDiskDirectPath_trace, monicKPrismNativeSharedTail_trace,
    List.cons_append]
  exact monicKPrismNativePasting_original_full_trace F f g n

/-- 元の全三角形・全交換セル・元の共有末尾から構成する端点固定実比較。 -/
def monicKPrismNativeFullPathComparison (n : ℕ) :=
  familyTriangleStripComparison
    (familyTriangleFirst (monicKPrismCompositionNativeTriangle n F f g))
    (familyTriangleDirect (monicKPrismCompositionNativeTriangle n F f g))
    (familyTriangleCompStruct (monicKPrismCompositionNativeTriangle n F f g))
    (monicKPrismNativeSecondCompatibilityTransport F f g n) (monicKPrismNativeSharedTail F f g n)

/-- 始点族は元の三角形の同じ始点で、全比較時刻を通して固定する。 -/
lemma monicKPrismNativeFullPathComparison_source (n : ℕ) :
    (SSet.ι₀ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismNativeFullPathComparison F f g n).h =
      CartesianMonoidalCategory.fst (nerve (CompositionStringParameters f g))
        (Δ[1] : SSet.{u}) ≫ SSet.ι₀ ≫
        (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 2) ≫
          monicKPrismCompositionNativeTriangle n F f g :=
  familyTriangleStripComparison_source _ _ _ _ _

/-- 終点族は元の次段 raw 合成評価の制限で、全比較時刻を通して固定する。 -/
lemma monicKPrismNativeFullPathComparison_target (n : ℕ) :
    (SSet.ι₁ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismNativeFullPathComparison F f g n).h =
      CartesianMonoidalCategory.fst (nerve (CompositionStringParameters f g))
        (Δ[1] : SSet.{u}) ≫ compositionStringPair f g ≫
        monicKPrismTracedRawComposition F f g ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z))
          (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
            ((kKanSequence (F.obj z)).level (n + 1)).space :=
  familyTriangleStripComparison_target _ _ _ _ _

end SerrePositivity.KST.SConstruction
