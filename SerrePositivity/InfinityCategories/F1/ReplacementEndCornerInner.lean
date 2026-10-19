module

public import SerrePositivity.InfinityCategories.F1.InnerPrismBoundaryExtension
public import SerrePositivity.InfinityCategories.F1.FullSubcomplexEquivalenceLifting
public import SerrePositivity.InfinityCategories.F1B.KanRelativeInternalHomLifting

/-!
概要：比較四角形の終点側の比較の内ホーン充填。
方針：始域の射影を先に持ち上げ、両端と底を固定した prism を延長する。
規約：可逆 path の族と元の四角形の比較を厳密に保つ。
使われ方：同時解像による比較立方体の終点側の相対比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 射影・相対内部 Hom・可逆 path 包含の持ち上げから、終点比較を持ち上げる。 -/
lemma hasLiftingProperty_replacementSquareEndCorner_of_lifting {A B X Y T U : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v)
    (i : T ⟶ U) [HasLiftingProperty i p]
    (hq : HasLiftingProperty i
      (Functor.PullbackObjObj.ofHasPullback internalHom (boundary 1).ι q).π)
    [HasLiftingProperty i (equivalencePathι X)] :
    HasLiftingProperty i (replacementSquareEndCorner u v p q h) := by
  constructor
  intro a b sq
  let aPath := a ≫ pullback.fst (equivalencePathEndpoint X 0) u
  let bPath := b ≫ pullback.snd q (equivalencePathReplacementMap v) ≫
    pullback.fst (equivalencePathEndpoint Y 0) v
  let a₀ := a ≫ equivalencePathReplacementProjection u
  let b₀ := b ≫ pullback.snd q (equivalencePathReplacementMap v) ≫
    equivalencePathReplacementProjection v
  let b₁ := b ≫ pullback.fst q (equivalencePathReplacementMap v)
  have ha : a ≫ replacementSquareMap u v p q h =
      i ≫ b ≫ pullback.snd q (equivalencePathReplacementMap v) := by
    have he := congrArg (fun m : T ⟶ pullback q (equivalencePathReplacementMap v) ↦
      m ≫ pullback.snd q (equivalencePathReplacementMap v)) sq.w
    rwa [Category.assoc, replacementSquareEndCorner_snd, Category.assoc] at he
  have hb : a ≫ equivalencePathReplacementMap u = i ≫ b₁ := by
    have he := congrArg (fun m : T ⟶ pullback q (equivalencePathReplacementMap v) ↦
      m ≫ pullback.fst q (equivalencePathReplacementMap v)) sq.w
    simpa only [b₁, Category.assoc, replacementSquareEndCorner_fst] using he
  have hw : a₀ ≫ p = i ≫ b₀ := by
    calc
      a₀ ≫ p = a ≫ (equivalencePathReplacementProjection u ≫ p) := Category.assoc _ _ _
      _ = a ≫ (replacementSquareMap u v p q h ≫ equivalencePathReplacementProjection v) := by
        rw [replacementSquareMap_projection]
      _ = (a ≫ replacementSquareMap u v p q h) ≫ equivalencePathReplacementProjection v :=
        (Category.assoc _ _ _).symm
      _ = (i ≫ b ≫ pullback.snd q (equivalencePathReplacementMap v)) ≫
          equivalencePathReplacementProjection v := by rw [ha]
      _ = i ≫ b₀ := by simp only [b₀, Category.assoc]
  let s : CommSq a₀ i p b₀ := ⟨hw⟩
  let f := s.lift
  let H := uncurry (aPath ≫ equivalencePathι X)
  let G := uncurry (bPath ≫ equivalencePathι Y)
  have hH₀ : prismEndpoint 0 T ≫ H = i ≫ (f ≫ u) := by
    rw [equivalencePathFamilyPrism_endpoint]
    change (a ≫ pullback.fst (equivalencePathEndpoint X 0) u) ≫
      equivalencePathEndpoint X 0 = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change a₀ ≫ u = i ≫ f ≫ u
    rw [← s.fac_left, Category.assoc]
  have hH₁ : prismEndpoint 1 T ≫ H = i ≫ b₁ := by
    rw [equivalencePathFamilyPrism_endpoint]
    change (a ≫ pullback.fst (equivalencePathEndpoint X 0) u) ≫
      equivalencePathEndpoint X 1 = _
    rw [Category.assoc]
    exact hb
  have hG₀ : prismEndpoint 0 U ≫ G = (f ≫ u) ≫ q := by
    rw [equivalencePathFamilyPrism_endpoint]
    change (b ≫ pullback.snd q (equivalencePathReplacementMap v) ≫
      pullback.fst (equivalencePathEndpoint Y 0) v) ≫ equivalencePathEndpoint Y 0 = _
    rw [Category.assoc, Category.assoc, pullback.condition]
    change b₀ ≫ v = (f ≫ u) ≫ q
    rw [← s.fac_right, Category.assoc, ← h, Category.assoc]
  have hG₁ : prismEndpoint 1 U ≫ G = b₁ ≫ q := by
    rw [equivalencePathFamilyPrism_endpoint]
    change (b ≫ pullback.snd q (equivalencePathReplacementMap v)) ≫
      equivalencePathReplacementMap v = (b ≫ pullback.fst q (equivalencePathReplacementMap v)) ≫ q
    simpa only [Category.assoc] using
      (congrArg (fun m : pullback q (equivalencePathReplacementMap v) ⟶ Y ↦ b ≫ m)
        (pullback.condition (f := q) (g := equivalencePathReplacementMap v))).symm
  have hsf : replacementSquareMap u v p q h ≫
      pullback.fst (equivalencePathEndpoint Y 0) v =
        pullback.fst (equivalencePathEndpoint X 0) u ≫ equivalencePathMap q :=
    relativePathSquareTargetMap_fst u v p q h 0
  have hPath : aPath ≫ equivalencePathMap q = i ≫ bPath := by
    calc
      aPath ≫ equivalencePathMap q = a ≫ (replacementSquareMap u v p q h ≫
          pullback.fst (equivalencePathEndpoint Y 0) v) := by
        dsimp only [aPath]
        rw [Category.assoc, hsf]
      _ = (a ≫ replacementSquareMap u v p q h) ≫
          pullback.fst (equivalencePathEndpoint Y 0) v := (Category.assoc _ _ _).symm
      _ = i ≫ bPath := by rw [ha]; simp only [bPath, Category.assoc]
  have hG : (Δ[1] ◁ i) ≫ G = H ≫ q := by
    apply curry_injective
    rw [curry_natural_left, curry_natural_right, curry_uncurry, curry_uncurry]
    calc
      i ≫ bPath ≫ equivalencePathι Y =
          (aPath ≫ equivalencePathMap q) ≫ equivalencePathι Y := by
        rw [hPath]
        simp only [bPath, Category.assoc]
      _ = (aPath ≫ equivalencePathι X) ≫ (ihom (Δ[1] : SSet.{u})).map q := by
        rw [Category.assoc, equivalencePathMap_ι, ← Category.assoc]
  obtain ⟨F, hF, hF₀, hF₁, hFq⟩ :=
    exists_prism_extension_over_fixed_endpoints_of_lifting q i hq
      H (f ≫ u) b₁ G hH₀ hH₁ hG hG₀ hG₁
  have sl : CommSq aPath i (equivalencePathι X) (curry F) := by
    constructor
    rw [← curry_natural_left, hF, curry_uncurry]
  let L := sl.lift
  have hL : L ≫ equivalencePathι X = curry F := sl.fac_right
  have hiL : i ≫ L = aPath := sl.fac_left
  have hL₀ : L ≫ equivalencePathEndpoint X 0 = f ≫ u := by
    change L ≫ equivalencePathι X ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = _
    rw [← Category.assoc, hL, curry_evaluateFunctorAt_interval, hF₀]
  have hL₁ : L ≫ equivalencePathEndpoint X 1 = b₁ := by
    change L ≫ equivalencePathι X ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = _
    rw [← Category.assoc, hL, curry_evaluateFunctorAt_interval, hF₁]
  have hLq : L ≫ equivalencePathMap q = bPath := by
    have : Mono (equivalencePathι Y) := by unfold equivalencePathι; infer_instance
    apply (cancel_mono (equivalencePathι Y)).mp
    rw [Category.assoc, equivalencePathMap_ι, ← Category.assoc, hL,
      ← curry_natural_right, hFq, curry_uncurry]
  let R := pullback.lift L f hL₀
  have hRf : R ≫ pullback.fst (equivalencePathEndpoint X 0) u = L := pullback.lift_fst _ _ _
  have hRs : R ≫ equivalencePathReplacementProjection u = f := pullback.lift_snd _ _ _
  refine CommSq.HasLift.mk' { l := R, fac_left := ?_, fac_right := ?_ }
  · apply pullback.hom_ext
    · rw [Category.assoc, hRf]
      exact hiL
    · change (i ≫ R) ≫ equivalencePathReplacementProjection u = a₀
      rw [Category.assoc, hRs]
      exact s.fac_left
  · apply pullback.hom_ext
    · rw [Category.assoc, replacementSquareEndCorner_fst]
      change R ≫ (pullback.fst (equivalencePathEndpoint X 0) u ≫
        equivalencePathEndpoint X 1) = b₁
      rw [← Category.assoc, hRf, hL₁]
    · rw [Category.assoc, replacementSquareEndCorner_snd]
      apply pullback.hom_ext
      · rw [Category.assoc, hsf, ← Category.assoc, hRf, hLq]
        simp only [bPath, Category.assoc]
      · change (R ≫ replacementSquareMap u v p q h) ≫
          equivalencePathReplacementProjection v = _
        rw [Category.assoc, replacementSquareMap_projection, ← Category.assoc, hRs]
        exact s.fac_right

/-- 両縦射が inner fibration なら、終点比較は内 anodyne な射を持ち上げる。 -/
lemma hasLiftingProperty_replacementSquareEndCorner {A B X Y T U : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v)
    [InnerFibration p] [InnerFibration q] (i : T ⟶ U) (hi : innerAnodyneExtensions i) :
    HasLiftingProperty i (replacementSquareEndCorner u v p q h) := by
  have : HasLiftingProperty i p := hi _ (mem_innerFibrations _)
  have : HasLiftingProperty i (equivalencePathι X) :=
    hasLiftingProperty_fullSubcomplexOnVertices_ι_of_vertex_surjective
      IsEquivalencePathVertex i (innerAnodyne_vertex_bijective i hi).surjective
  let r := Functor.PullbackObjObj.ofHasPullback internalHom (boundary 1).ι q
  have : InnerFibration r.π := innerFibration_pullbackObjObjπ r
  exact hasLiftingProperty_replacementSquareEndCorner_of_lifting u v p q h i
    (hi _ (mem_innerFibrations r.π))

/-- 両縦射の前合成同値の持ち上げは、終点比較にも伝わる。 -/
lemma kanEquivalenceLifting_replacementSquareEndCorner {A B X Y : SSet.{u}}
    [Quasicategory X] (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y)
    (h : u ≫ q = p ≫ v) (hp : F1B.KanEquivalenceLifting p)
    (hq : F1B.KanEquivalenceLifting q) :
    F1B.KanEquivalenceLifting (replacementSquareEndCorner u v p q h) := by
  intro T U i hm hi
  have : Mono i := hm
  have := hp i hm hi
  have := kanEquivalenceLifting_equivalencePathι X i hm hi
  let r := Functor.PullbackObjObj.ofHasPullback internalHom (boundary 1).ι q
  exact hasLiftingProperty_replacementSquareEndCorner_of_lifting u v p q h i
    (F1B.KanEquivalenceLifting.relativeInternalHom hq (boundary 1).ι r i hm hi)

/-- 両縦射が inner fibration の比較四角形の終点比較も inner fibration。 -/
instance replacementSquareEndCorner_innerFibration {A B X Y : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v)
    [InnerFibration p] [InnerFibration q] :
    InnerFibration (replacementSquareEndCorner u v p q h) := by
  constructor
  intro T U i hi
  cases hi with
  | @intro n k h0 hn =>
    exact hasLiftingProperty_replacementSquareEndCorner u v p q h _
      (innerAnodyneExtensions.horn_ι h0 hn)

end SerrePositivity.InfinityCategories
