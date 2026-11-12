module
public import SerrePositivity.KST.SConstruction.ArCofiberSpanInputs

/-! # span 全体と枠を保つ cofiber 補完
概要：全区間の入力 span と既存の gapped 境界、枠を同時に固定して cofiber を選ぶ。
方針：枠包含と零脚つき span 射影の相対内部 Hom の trivial Kan fibration を使う。
規約：得られた右上角の図式の gapped 性を仮定しない。
使われ方：BGT Lemma 7.3 の第一行からの復元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：境界と枠と全 span を厳密に保つ cofiber の族が存在する。
方針：枠包含と cofiberSpanProjection の相対内部 Hom で任意の単射を持ち上げる。
規約：C は安定な quasicategory。追加の余極限の存在仮定を使わない。
使われ方：零射の coherent な指定を含む Ar[n] 上の相対補完。 -/
lemma exists_arCofiberSpanCompletion_preserving_frame {A B C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (n : ℕ) (i : A ⟶ B) [Mono i]
    (a : A ⟶ sConstruction n C) (b : B ⟶ zeroFrameDiagrams n C)
    (h : a ≫ gappedFrameRestriction n C = i ≫ b) :
    ∃ H : B ⟶ (ihom (arNerve n)).obj (cofiberDiagrams C),
      i ≫ H = a ≫ gappedCofiberFamiliesMap n C ∧
      H ≫ (ihom (arNerve n)).map (cofiberSpanProjection C) = b ≫ frameCofiberSpans n C ∧
      H ≫ (pre (frameInclusion n)).app (cofiberDiagrams C) =
        b ≫ zeroFrameCofiberFamiliesMap n C := by
  let sq := Functor.PullbackObjObj.ofHasPullback internalHom (frameInclusion n) (cofiberSpanProjection C)
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration sq.π :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.trivialKanFibration_pullbackObjObjπ (frameInclusion n) (cofiberSpanProjection C) sq
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := sq.π) i inferInstance
  let d : B ⟶ sq.pt := sq.isPullback.lift (b ≫ zeroFrameCofiberFamiliesMap n C)
    (b ≫ frameCofiberSpans n C) (by
      change (b ≫ zeroFrameCofiberFamiliesMap n C) ≫
        (ihom (frameNerve n)).map (cofiberSpanProjection C) =
        (b ≫ frameCofiberSpans n C) ≫
          (pre (frameInclusion n)).app (zeroSpanDiagrams C)
      rw [Category.assoc, zeroFrameCofiberFamiliesMap_span, Category.assoc])
  have hd₁ : d ≫ sq.fst = b ≫ zeroFrameCofiberFamiliesMap n C := sq.isPullback.lift_fst _ _ _
  have hd₂ : d ≫ sq.snd = b ≫ frameCofiberSpans n C := sq.isPullback.lift_snd _ _ _
  have hs : CommSq (a ≫ gappedCofiberFamiliesMap n C) i sq.π d := by
    constructor
    apply sq.hom_ext
    · simp only [Category.assoc, sq.π_fst, hd₁]
      change a ≫ gappedCofiberFamiliesMap n C ≫
        (pre (frameInclusion n)).app (cofiberDiagrams C) = _
      rw [gappedCofiberFamiliesMap_frame, ← Category.assoc, h, Category.assoc]
    · simp only [Category.assoc, sq.π_snd, hd₂]
      change a ≫ gappedCofiberFamiliesMap n C ≫
        (ihom (arNerve n)).map (cofiberSpanProjection C) = _
      rw [gappedCofiberFamiliesMap_span, ← Category.assoc, h, Category.assoc]
  have hinput : hs.lift ≫ (ihom (arNerve n)).map (cofiberSpanProjection C) =
      b ≫ frameCofiberSpans n C := by
    have he := congrArg (fun f => f ≫ sq.snd) hs.fac_right
    rw [Category.assoc, sq.π_snd, hd₂] at he
    exact he
  refine ⟨hs.lift, hs.fac_left, hinput, ?_⟩
  have he := congrArg (fun f => f ≫ sq.fst) hs.fac_right
  rw [Category.assoc, sq.π_fst, hd₁] at he
  exact he

end SerrePositivity.KST.SConstruction
