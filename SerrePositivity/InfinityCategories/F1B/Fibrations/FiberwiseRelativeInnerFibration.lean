module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeHomDiagramOverExtension
public import SerrePositivity.InfinityCategories.F1B.Fibrations.FiberwiseRelativeRestriction
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinInvertingRestriction

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
lemma fiberwiseRelativeRestriction_innerFibration {C D E : SSet.{u}}
    {K L : Over C} (i : K ⟶ L) [Mono i.left]
    [CocartesianFibration K.hom] [CocartesianFibration L.hom] (U : D ⟶ E)
    (hU : ∀ {X Y : SSet.{u}} (m : X ⟶ Y), Mono m →
      IsPrecompositionEquivalence m → HasLiftingProperty m U) :
    InnerFibration (SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction i U) where
  mem := by
    intro A B j hj
    constructor
    intro a b sq
    let c := b ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeProjection i U
    let f := b ≫ pullback.fst (SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp K.hom U)
      (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := E) i)
    let g := b ≫ pullback.snd (SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp K.hom U)
      (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := E) i)
    have hf : f ≫ SerrePositivity.InfinityCategories.fiberwiseHomProjection K.hom D = c := by
      dsimp only [f, c, SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeProjection]
      exact Category.assoc _ _ _
    have hg : g ≫ SerrePositivity.InfinityCategories.fiberwiseHomProjection L.hom E = c := by
      dsimp only [g, c]
      rw [Category.assoc, ← SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeProjection_snd]
    have ha : a ≫ SerrePositivity.InfinityCategories.fiberwiseHomProjection L.hom D = j ≫ c := by
      rw [← SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction_projection i U, ← Category.assoc, sq.w,
        Category.assoc]
    let F := (SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := D) K.hom c).symm ⟨f, hf⟩
    let G := (SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := D) L.hom (j ≫ c)).symm ⟨a, ha⟩
    let H₀ := (SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := E) L.hom c).symm ⟨g, hg⟩
    have hF : SerrePositivity.InfinityCategories.fiberwiseHomCurry K.hom c F = f :=
      congrArg Subtype.val ((SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := D) K.hom c).apply_symm_apply ⟨f, hf⟩)
    have hG : SerrePositivity.InfinityCategories.fiberwiseHomCurry L.hom (j ≫ c) G = a :=
      congrArg Subtype.val ((SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := D) L.hom (j ≫ c)).apply_symm_apply ⟨a, ha⟩)
    have hH₀ : SerrePositivity.InfinityCategories.fiberwiseHomCurry L.hom c H₀ = g :=
      congrArg Subtype.val ((SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := E) L.hom c).apply_symm_apply ⟨g, hg⟩)
    let u : Over.mk (j ≫ c) ⟶ Over.mk c := Over.homMk j rfl
    have hFG : (overPullbackUnderlying K.hom).map u ≫ F =
        overPullbackMap i (Over.mk (j ≫ c)) ≫ G := by
      apply SerrePositivity.InfinityCategories.fiberwiseHomCurry_injective K.hom (j ≫ c)
      erw [SerrePositivity.InfinityCategories.fiberwiseHomCurry_precomp, kanFiberwiseHomCurry_pre i, hF, hG]
      have h := congrArg (fun z ↦ z ≫ pullback.fst (SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp K.hom U)
        (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := E) i)) sq.w
      simpa only [Category.assoc, SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction_fst] using h.symm
    have hFU : F ≫ U = overPullbackMap i (Over.mk c) ≫ H₀ := by
      apply SerrePositivity.InfinityCategories.fiberwiseHomCurry_injective K.hom c
      calc
        SerrePositivity.InfinityCategories.fiberwiseHomCurry K.hom c (F ≫ U) =
            SerrePositivity.InfinityCategories.fiberwiseHomCurry K.hom c F ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp K.hom U :=
          SerrePositivity.InfinityCategories.F1B.fiberwiseHomCurry_postcomp K.hom U c F
        _ = f ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp K.hom U :=
          congrArg (· ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp K.hom U) hF
        _ = g ≫ SerrePositivity.InfinityCategories.fiberwiseHomPre (D := E) i := by
          dsimp only [f, g]
          rw [Category.assoc, Category.assoc, pullback.condition]
        _ = SerrePositivity.InfinityCategories.fiberwiseHomCurry L.hom c H₀ ≫ SerrePositivity.InfinityCategories.fiberwiseHomPre (D := E) i :=
          congrArg (· ≫ SerrePositivity.InfinityCategories.fiberwiseHomPre (D := E) i) hH₀.symm
        _ = _ := (kanFiberwiseHomCurry_pre i c H₀).symm
    have hGU : G ≫ U = (overPullbackUnderlying L.hom).map u ≫ H₀ := by
      apply SerrePositivity.InfinityCategories.fiberwiseHomCurry_injective L.hom (j ≫ c)
      calc
        SerrePositivity.InfinityCategories.fiberwiseHomCurry L.hom (j ≫ c) (G ≫ U) =
            SerrePositivity.InfinityCategories.fiberwiseHomCurry L.hom (j ≫ c) G ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp L.hom U :=
          SerrePositivity.InfinityCategories.F1B.fiberwiseHomCurry_postcomp L.hom U (j ≫ c) G
        _ = a ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp L.hom U :=
          congrArg (· ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp L.hom U) hG
        _ = j ≫ g := by
          have h := congrArg (fun z ↦ z ≫ pullback.snd (SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp K.hom U)
            (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := E) i)) sq.w
          simpa only [Category.assoc, SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction_snd] using h
        _ = j ≫ SerrePositivity.InfinityCategories.fiberwiseHomCurry L.hom c H₀ := congrArg (j ≫ ·) hH₀.symm
        _ = _ := (SerrePositivity.InfinityCategories.fiberwiseHomCurry_precomp L.hom j c H₀).symm
    obtain ⟨H, hHK, hHL, hHU⟩ :=
      exists_kanRelativeHomDiagram_extension_over i u hj U hU F G H₀ hFG hFU hGU
    refine CommSq.HasLift.mk' {
      l := SerrePositivity.InfinityCategories.fiberwiseHomCurry L.hom c H
      fac_left := ?_
      fac_right := ?_ }
    · rw [← SerrePositivity.InfinityCategories.fiberwiseHomCurry_precomp]
      change SerrePositivity.InfinityCategories.fiberwiseHomCurry L.hom (j ≫ c) ((overPullbackUnderlying L.hom).map u ≫ H) = _
      rw [hHL, hG]
    · apply pullback.hom_ext
      · rw [Category.assoc, SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction_fst,
          ← kanFiberwiseHomCurry_pre i, hHK, hF]
      · rw [Category.assoc, SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction_snd,
          ← SerrePositivity.InfinityCategories.F1B.fiberwiseHomCurry_postcomp, hHU, hH₀]

/-- 概要：単射による関手の制限を標的の射とする全空間の相対比較は inner fibration。
方針：単射な前合成同値に対する関手の制限の持ち上げ性を一般の判定へ渡す。
規約：X は quasicategory、境界を含む任意の単射 v を扱う。
使われ方：写像空間の制限定理の V′ の全空間での充填性。 -/
instance fiberwiseRelativeRestriction_pre_innerFibration {C P Q X : SSet.{u}}
    [Quasicategory X] {K L : Over C} (i : K ⟶ L) [Mono i.left]
    [CocartesianFibration K.hom] [CocartesianFibration L.hom]
    (v : P ⟶ Q) [Mono v] : InnerFibration (SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction i ((pre v).app X)) := by
  apply fiberwiseRelativeRestriction_innerFibration
  intro Y Z m hm he
  have : Mono m := hm
  exact he.hasLiftingProperty_pre v X

end SerrePositivity.InfinityCategories.F1B
