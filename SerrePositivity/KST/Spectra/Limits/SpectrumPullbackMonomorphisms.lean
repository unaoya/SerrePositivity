module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.SmashMonomorphisms
public import SerrePositivity.KST.Spectra.Limits.SpectrumBinaryProduct
public import SerrePositivity.KST.Spectra.PullbackKanSequence

/-!
概要：スペクトルの段ごとの引き戻しの構造射の単射性。
方針：引き戻しを二項積に包含し、懸垂の単射保存と積の構造射の単射性へ帰着する。
規約：このファイルでは Ω 条件と ∞ 極限性はまだ主張しない。
使われ方：BF 1978 §2、HTT 4.2.4.1 の Sp の実際の引き戻し対象の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：点つき引き戻しを二つの射影で通常積に包含する標準射。
方針：引き戻しの二つの射影を積の普遍性で組にする。
規約：元の cospan の射に fibration 性を仮定しない。
使われ方：懸垂の構造射の単射性を積で検査する。 -/
def pointedPullbackToProduct {E X B : PointedSimplicialSet.{u}} (f : E ⟶ B) (g : X ⟶ B) :
    pullback f g ⟶ PointedObject.prod E X :=
  PointedObject.prodLift (pullback.fst f g) (pullback.snd f g)

/-- 概要：引き戻しから積への標準射の基礎単体写像はモノ射。
方針：基礎の引き戻しの普遍性により二つの射影で射を識別する。
規約：Kan 性と fibration 性は不要。
使われ方：懸垂に引き戻しの包含の単射性を渡す。 -/
instance pointedPullbackToProduct_mono {E X B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (g : X ⟶ B) : Mono (pointedPullbackToProduct f g).right := ⟨by
  intro Z a b h
  apply (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback f g).hom_ext
  · have h' := congrArg (fun k ↦ k ≫ (PointedObject.prodFst E X).right) h
    have he := congrArg Under.Hom.right
      (PointedObject.prodLift_fst (pullback.fst f g) (pullback.snd f g))
    change (pointedPullbackToProduct f g).right ≫ (PointedObject.prodFst E X).right = _ at he
    simpa only [Category.assoc, he] using h'
  · have h' := congrArg (fun k ↦ k ≫ (PointedObject.prodSnd E X).right) h
    have he := congrArg Under.Hom.right
      (PointedObject.prodLift_snd (pullback.fst f g) (pullback.snd f g))
    change (pointedPullbackToProduct f g).right ≫ (PointedObject.prodSnd E X).right = _ at he
    simpa only [Category.assoc, he] using h'⟩

/-- 概要：引き戻し列の構造射は積への包含と積の構造射に関して可換。
方針：積の二つの射影の後で計算し、懸垂の合成保存を使う。
規約：Kan 列の元の厳密な構造射を用い、fibration 性は要求しない。
使われ方：引き戻しの構造射の単射性の検証。 -/
lemma pullbackSigma_product_factor {E X B : KanSequence.{u}}
    (f : KanSequence.Hom E B) (g : KanSequence.Hom X B) (n : ℕ) :
    KanSequence.pullbackSigma f g n ≫
        pointedPullbackToProduct (f.app (n + 1)) (g.app (n + 1)) =
      PointedSimplicialSet.circle.{u} ◁ pointedPullbackToProduct (f.app n) (g.app n) ≫
        binaryProductSigma (E.sigma n) (X.sigma n) := by
  apply PointedObject.prod_hom_ext <;>
    simp only [pointedPullbackToProduct, binaryProductSigma, Category.assoc,
      PointedObject.prodLift_fst, PointedObject.prodLift_snd, KanSequence.pullbackSigma,
      pullback.lift_fst, pullback.lift_snd, ← whiskerLeft_comp_assoc,
      PointedObject.prodLift_fst, PointedObject.prodLift_snd]

/-- 概要：二つの列の構造射が単射なら、その段ごとの引き戻しの構造射も単射。
方針：積への包含後の射を懸垂した包含と積の構造射の合成に分解する。
規約：底の列の構造射や元の射の fibration 性に条件を置かない。
使われ方：L9 の OmegaSpectrum の引き戻しで sigma_mono 条件を検証する。 -/
lemma pullbackSigma_mono {E X B : KanSequence.{u}}
    (f : KanSequence.Hom E B) (g : KanSequence.Hom X B)
    (hE : ∀ n, Mono (E.sigma n).right) (hX : ∀ n, Mono (X.sigma n).right) (n : ℕ) :
    Mono (KanSequence.pullbackSigma f g n).right := by
  have := hE n
  have := hX n
  have hc := congrArg Under.Hom.right (pullbackSigma_product_factor f g n)
  simp only [Under.comp_right] at hc
  have h : Mono ((KanSequence.pullbackSigma f g n).right ≫
      (pointedPullbackToProduct (f.app (n + 1)) (g.app (n + 1))).right) := by
    rw [hc]
    change Mono ((PointedSimplicialSet.circle.{u} ◁
      pointedPullbackToProduct (f.app n) (g.app n)).right ≫
        (binaryProductSigma (E.sigma n) (X.sigma n)).right)
    infer_instance
  exact mono_of_mono (KanSequence.pullbackSigma f g n).right
    (pointedPullbackToProduct (f.app (n + 1)) (g.app (n + 1))).right

end
end SerrePositivity.InfinityCategories.HomotopyLimits
