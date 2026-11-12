module
public import SerrePositivity.KST.SConstruction.FrameCofiberCompatibility
public import SerrePositivity.KST.SConstruction.ArCofiberCompletion
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeInternalHomTrivialFibration

/-! # 境界と枠を同時に固定した cofiber 補完
概要：Ar[n] 上の cofiber 族を、既存境界と零対角の枠の両方を厳密に保って補完する。
方針：単射と cofiber 射影の相対内部 Hom の trivial Kan fibration を使う。
規約：出力の gapped 条件は別に証明する。使われ方：BGT Lemma 7.3、HTT §4.3.2。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：第一行と対角の枠の包含は単射。
方針：各次数の鎖の頂点の等号を部分型の等号に戻す。
規約：全ての次数で単射。使われ方：相対内部 Hom の持ち上げ。 -/
instance frameInclusion_mono (n : ℕ) : Mono (frameInclusion.{u} n) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [mono_iff_injective]
  intro s t h
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  exact Subtype.ext (congrArg (fun f : (arNerve n).obj d => f.obj r) h)

/-- 概要：cofiber 補完は境界だけでなく枠の全ての単体を厳密に保つよう選べる。
方針：枠包含と cofiber 射影の相対内部 Hom の全単射持ち上げを使う。
規約：i は任意の単射、C は安定な quasicategory。
使われ方：第一行を変更せずに Ar[n] の残りを補完する。 -/
lemma exists_arCofiberCompletion_preserving_frame {A B C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (n : ℕ) (i : A ⟶ B) [Mono i]
    (a : A ⟶ sConstruction n C) (b : B ⟶ zeroFrameDiagrams n C)
    (h : a ≫ gappedFrameRestriction n C = i ≫ b) :
    ∃ c : ArCofiberCompletion n i a b,
      c.family ≫ (pre (frameInclusion n)).app (cofiberDiagrams C) =
        b ≫ zeroFrameCofiberFamiliesMap n C := by
  let sq := Functor.PullbackObjObj.ofHasPullback internalHom (frameInclusion n) (cofiberProjection C)
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration sq.π :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.trivialKanFibration_pullbackObjObjπ (frameInclusion n) (cofiberProjection C) sq
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := sq.π) i inferInstance
  let d : B ⟶ sq.pt := sq.isPullback.lift (b ≫ zeroFrameCofiberFamiliesMap n C)
    (b ≫ frameCofiberInputs n C) (by
      change (b ≫ zeroFrameCofiberFamiliesMap n C) ≫
        (ihom (frameNerve n)).map (cofiberProjection C) =
        (b ≫ frameCofiberInputs n C) ≫
          (pre (frameInclusion n)).app ((ihom (Δ[1] : SSet.{u})).obj C)
      rw [Category.assoc, zeroFrameCofiberFamiliesMap_input, Category.assoc])
  have hd₁ : d ≫ sq.fst = b ≫ zeroFrameCofiberFamiliesMap n C := sq.isPullback.lift_fst _ _ _
  have hd₂ : d ≫ sq.snd = b ≫ frameCofiberInputs n C := sq.isPullback.lift_snd _ _ _
  have hs : CommSq (a ≫ gappedCofiberFamiliesMap n C) i sq.π d := by
    constructor
    apply sq.hom_ext
    · simp only [Category.assoc, sq.π_fst, hd₁]
      change a ≫ gappedCofiberFamiliesMap n C ≫
        (pre (frameInclusion n)).app (cofiberDiagrams C) = _
      rw [gappedCofiberFamiliesMap_frame, ← Category.assoc, h, Category.assoc]
    · simp only [Category.assoc, sq.π_snd, hd₂]
      change a ≫ gappedCofiberFamiliesMap n C ≫
        (ihom (arNerve n)).map (cofiberProjection C) = _
      rw [gappedCofiberFamiliesMap_input, ← Category.assoc, h, Category.assoc]
  have hinput : hs.lift ≫ (ihom (arNerve n)).map (cofiberProjection C) =
      b ≫ frameCofiberInputs n C := by
    have he := congrArg (fun f => f ≫ sq.snd) hs.fac_right
    rw [Category.assoc, sq.π_snd, hd₂] at he
    exact he
  refine ⟨⟨hs.lift, hs.fac_left, hinput⟩, ?_⟩
  have he := congrArg (fun f => f ≫ sq.fst) hs.fac_right
  rw [Category.assoc, sq.π_fst, hd₁] at he
  exact he

/-- 概要：枠を保つ cofiber 族の補完は、右上角の図式も元の枠と厳密に一致する。
方針：前合成と後合成の自然性、および枠の右上角の回収を使う。
規約：第一行を含む枠の全次数での等号。使われ方：第一行制限の RLP の右側の等号。 -/
lemma ArCofiberCompletion.diagram_frame {A B C : SSet.{u}} [Quasicategory C]
    {n : ℕ} {i : A ⟶ B} {a : A ⟶ sConstruction n C} {b : B ⟶ zeroFrameDiagrams n C}
    (c : ArCofiberCompletion n i a b)
    (hc : c.family ≫ (pre (frameInclusion n)).app (cofiberDiagrams C) =
      b ≫ zeroFrameCofiberFamiliesMap n C) :
    c.diagram ≫ (pre (frameInclusion n)).app C =
      b ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroFrameVertex).ι := by
  rw [ArCofiberCompletion.diagram, Category.assoc, (pre (frameInclusion n)).naturality,
    ← Category.assoc, hc, Category.assoc, zeroFrameCofiberFamiliesMap_apex]

/-- 概要：枠を保つ cofiber 補完の右上角の図式は、全ての対角で零対象となる。
方針：枠への制限の厳密な等号を頂点で評価し、元の枠の零対角条件を使う。
規約：境界が全頂点を含むことや安定性は要求しない。
使われ方：零次元で新しく作る図式の gapped 条件の対角部分。 -/
lemma ArCofiberCompletion.diagram_zero_diagonal {A B C : SSet.{u}} [Quasicategory C]
    {n : ℕ} {i : A ⟶ B} {a : A ⟶ sConstruction n C} {b : B ⟶ zeroFrameDiagrams n C}
    (c : ArCofiberCompletion n i a b)
    (hc : c.family ≫ (pre (frameInclusion n)).app (cofiberDiagrams C) =
      b ≫ zeroFrameCofiberFamiliesMap n C) (v : B _⦋0⦌) (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).symm
      (c.diagram.app (Opposite.op ⦋0⦌) v)).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ (arObj j j le_rfl))) := by
  let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).symm (c.diagram.app (Opposite.op ⦋0⦌) v)
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = c.diagram.app (Opposite.op ⦋0⦌) v :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (c.diagram_frame hc) (Opposite.op ⦋0⦌)) v
  change ((pre (frameInclusion n)).app C).app (Opposite.op ⦋0⦌)
    (c.diagram.app (Opposite.op ⦋0⦌) v) = (b.app (Opposite.op ⦋0⦌) v).val at he
  rw [← hF] at he
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (frameInclusion n ≫ F) = (b.app (Opposite.op ⦋0⦌) v).val at he
  have hz : IsZeroFrameVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (frameInclusion n ≫ F)) := by
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (b.app (Opposite.op ⦋0⦌) v)
  have h := hz (ComposableArrows.mk₀ (⟨arObj j j le_rfl, Or.inr rfl⟩ : FrameAr n)) rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at h
  exact h

end SerrePositivity.KST.SConstruction
