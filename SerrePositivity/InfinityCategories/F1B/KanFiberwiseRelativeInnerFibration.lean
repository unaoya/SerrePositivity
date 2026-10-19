module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeHomDiagramOverExtension
public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseRelativeRestriction
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinInvertingRestriction

/-!
概要：全空間の相対比較の内ホーン充填を構成する。
方針：curry の全単射で三つの指定を逆像上の図式へ戻し、相対延長後に curry する。
規約：標的の射の持ち上げ条件は明示し、関手の制限については既存定理で充足する。
使われ方：fiber の相対余錐条件を全空間へ移送する際の inner fibration の前提。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：部分図式と標的の全図式を指定する全空間の相対比較は inner fibration。
方針：可換正方形を三つの整合する図式へ変換し、標的を保つ内ホーン延長を使う。
規約：標的の射は単射な前合成同値に対する持ち上げを持つ。
使われ方：相対 Kan の局所普遍性から全空間の境界充填を得るための前提。 -/
lemma kanFiberwiseRelativeRestriction_innerFibration {C D E : SSet.{u}}
    {K L : Over C} (i : K ⟶ L) [Mono i.left]
    [CocartesianFibration K.hom] [CocartesianFibration L.hom] (U : D ⟶ E)
    (hU : ∀ {X Y : SSet.{u}} (m : X ⟶ Y), Mono m →
      IsPrecompositionEquivalence m → HasLiftingProperty m U) :
    InnerFibration (kanFiberwiseRelativeRestriction i U) where
  mem := by
    intro A B j hj
    constructor
    intro a b sq
    let c := b ≫ kanFiberwiseRelativeProjection i U
    let f := b ≫ pullback.fst (kanFiberwiseHomPostcomp K.hom U)
      (kanFiberwiseHomPre (D := E) i)
    let g := b ≫ pullback.snd (kanFiberwiseHomPostcomp K.hom U)
      (kanFiberwiseHomPre (D := E) i)
    have hf : f ≫ kanFiberwiseHomProjection K.hom D = c := by
      dsimp only [f, c, kanFiberwiseRelativeProjection]
      exact Category.assoc _ _ _
    have hg : g ≫ kanFiberwiseHomProjection L.hom E = c := by
      dsimp only [g, c]
      rw [Category.assoc, ← kanFiberwiseRelativeProjection_snd]
    have ha : a ≫ kanFiberwiseHomProjection L.hom D = j ≫ c := by
      rw [← kanFiberwiseRelativeRestriction_projection i U, ← Category.assoc, sq.w,
        Category.assoc]
    let F := (kanFiberwiseHomEquiv (D := D) K.hom c).symm ⟨f, hf⟩
    let G := (kanFiberwiseHomEquiv (D := D) L.hom (j ≫ c)).symm ⟨a, ha⟩
    let H₀ := (kanFiberwiseHomEquiv (D := E) L.hom c).symm ⟨g, hg⟩
    have hF : kanFiberwiseHomCurry K.hom c F = f :=
      congrArg Subtype.val ((kanFiberwiseHomEquiv (D := D) K.hom c).apply_symm_apply ⟨f, hf⟩)
    have hG : kanFiberwiseHomCurry L.hom (j ≫ c) G = a :=
      congrArg Subtype.val ((kanFiberwiseHomEquiv (D := D) L.hom (j ≫ c)).apply_symm_apply ⟨a, ha⟩)
    have hH₀ : kanFiberwiseHomCurry L.hom c H₀ = g :=
      congrArg Subtype.val ((kanFiberwiseHomEquiv (D := E) L.hom c).apply_symm_apply ⟨g, hg⟩)
    let u : Over.mk (j ≫ c) ⟶ Over.mk c := Over.homMk j rfl
    have hFG : (overPullbackUnderlying K.hom).map u ≫ F =
        overPullbackMap i (Over.mk (j ≫ c)) ≫ G := by
      apply kanFiberwiseHomCurry_injective K.hom (j ≫ c)
      erw [kanFiberwiseHomCurry_precomp, kanFiberwiseHomCurry_pre i, hF, hG]
      have h := congrArg (fun z ↦ z ≫ pullback.fst (kanFiberwiseHomPostcomp K.hom U)
        (kanFiberwiseHomPre (D := E) i)) sq.w
      simpa only [Category.assoc, kanFiberwiseRelativeRestriction_fst] using h.symm
    have hFU : F ≫ U = overPullbackMap i (Over.mk c) ≫ H₀ := by
      apply kanFiberwiseHomCurry_injective K.hom c
      calc
        kanFiberwiseHomCurry K.hom c (F ≫ U) =
            kanFiberwiseHomCurry K.hom c F ≫ kanFiberwiseHomPostcomp K.hom U :=
          kanFiberwiseHomCurry_postcomp K.hom U c F
        _ = f ≫ kanFiberwiseHomPostcomp K.hom U :=
          congrArg (· ≫ kanFiberwiseHomPostcomp K.hom U) hF
        _ = g ≫ kanFiberwiseHomPre (D := E) i := by
          dsimp only [f, g]
          rw [Category.assoc, Category.assoc, pullback.condition]
        _ = kanFiberwiseHomCurry L.hom c H₀ ≫ kanFiberwiseHomPre (D := E) i :=
          congrArg (· ≫ kanFiberwiseHomPre (D := E) i) hH₀.symm
        _ = _ := (kanFiberwiseHomCurry_pre i c H₀).symm
    have hGU : G ≫ U = (overPullbackUnderlying L.hom).map u ≫ H₀ := by
      apply kanFiberwiseHomCurry_injective L.hom (j ≫ c)
      calc
        kanFiberwiseHomCurry L.hom (j ≫ c) (G ≫ U) =
            kanFiberwiseHomCurry L.hom (j ≫ c) G ≫ kanFiberwiseHomPostcomp L.hom U :=
          kanFiberwiseHomCurry_postcomp L.hom U (j ≫ c) G
        _ = a ≫ kanFiberwiseHomPostcomp L.hom U :=
          congrArg (· ≫ kanFiberwiseHomPostcomp L.hom U) hG
        _ = j ≫ g := by
          have h := congrArg (fun z ↦ z ≫ pullback.snd (kanFiberwiseHomPostcomp K.hom U)
            (kanFiberwiseHomPre (D := E) i)) sq.w
          simpa only [Category.assoc, kanFiberwiseRelativeRestriction_snd] using h
        _ = j ≫ kanFiberwiseHomCurry L.hom c H₀ := congrArg (j ≫ ·) hH₀.symm
        _ = _ := (kanFiberwiseHomCurry_precomp L.hom j c H₀).symm
    obtain ⟨H, hHK, hHL, hHU⟩ :=
      exists_kanRelativeHomDiagram_extension_over i u hj U hU F G H₀ hFG hFU hGU
    refine CommSq.HasLift.mk' {
      l := kanFiberwiseHomCurry L.hom c H
      fac_left := ?_
      fac_right := ?_ }
    · rw [← kanFiberwiseHomCurry_precomp]
      change kanFiberwiseHomCurry L.hom (j ≫ c) ((overPullbackUnderlying L.hom).map u ≫ H) = _
      rw [hHL, hG]
    · apply pullback.hom_ext
      · rw [Category.assoc, kanFiberwiseRelativeRestriction_fst,
          ← kanFiberwiseHomCurry_pre i, hHK, hF]
      · rw [Category.assoc, kanFiberwiseRelativeRestriction_snd,
          ← kanFiberwiseHomCurry_postcomp, hHU, hH₀]

/-- 概要：単射による関手の制限を標的の射とする全空間の相対比較は inner fibration。
方針：単射な前合成同値に対する関手の制限の持ち上げ性を一般の判定へ渡す。
規約：X は quasicategory、境界を含む任意の単射 v を扱う。
使われ方：写像空間の制限定理の V′ の全空間での充填性。 -/
instance kanFiberwiseRelativeRestriction_pre_innerFibration {C P Q X : SSet.{u}}
    [Quasicategory X] {K L : Over C} (i : K ⟶ L) [Mono i.left]
    [CocartesianFibration K.hom] [CocartesianFibration L.hom]
    (v : P ⟶ Q) [Mono v] : InnerFibration (kanFiberwiseRelativeRestriction i ((pre v).app X)) := by
  apply kanFiberwiseRelativeRestriction_innerFibration
  intro Y Z m hm he
  have : Mono m := hm
  exact he.hasLiftingProperty_pre v X

end SerrePositivity.InfinityCategories.F1B
