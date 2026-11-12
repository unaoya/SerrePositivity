module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.InnerPrismBoundaryExtension
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullSubcomplexEquivalenceLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeInternalHomLifting

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
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 射影・相対内部 Hom・可逆 path 包含の持ち上げから、終点比較を持ち上げる。 -/
lemma hasLiftingProperty_replacementSquareEndCorner_of_lifting {A B X Y T U : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v)
    (i : T ⟶ U) [HasLiftingProperty i p]
    (hq : HasLiftingProperty i
      (Functor.PullbackObjObj.ofHasPullback internalHom (boundary 1).ι q).π)
    [HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X)] :
    HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareEndCorner u v p q h) := by
  constructor
  intro a b sq
  let aPath := a ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) u
  let bPath := b ≫ pullback.snd q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v) ≫
    pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) v
  let a₀ := a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection u
  let b₀ := b ≫ pullback.snd q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v
  let b₁ := b ≫ pullback.fst q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v)
  have ha : a ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u v p q h =
      i ≫ b ≫ pullback.snd q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v) := by
    have he := congrArg (fun m : T ⟶ pullback q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v) ↦
      m ≫ pullback.snd q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v)) sq.w
    rwa [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareEndCorner_snd, Category.assoc] at he
  have hb : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap u = i ≫ b₁ := by
    have he := congrArg (fun m : T ⟶ pullback q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v) ↦
      m ≫ pullback.fst q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v)) sq.w
    simpa only [b₁, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareEndCorner_fst] using he
  have hw : a₀ ≫ p = i ≫ b₀ := by
    calc
      a₀ ≫ p = a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection u ≫ p) := Category.assoc _ _ _
      _ = a ≫ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u v p q h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v) := by
        rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap_projection]
      _ = (a ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u v p q h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v :=
        (Category.assoc _ _ _).symm
      _ = (i ≫ b ≫ pullback.snd q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v := by rw [ha]
      _ = i ≫ b₀ := by simp only [b₀, Category.assoc]
  let s : CommSq a₀ i p b₀ := ⟨hw⟩
  let f := s.lift
  let H := uncurry (aPath ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X)
  let G := uncurry (bPath ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y)
  have hH₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 T ≫ H = i ≫ (f ≫ u) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.equivalencePathFamilyPrism_endpoint]
    change (a ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) u) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0 = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change a₀ ≫ u = i ≫ f ≫ u
    rw [← s.fac_left, Category.assoc]
  have hH₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 T ≫ H = i ≫ b₁ := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.equivalencePathFamilyPrism_endpoint]
    change (a ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) u) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 1 = _
    rw [Category.assoc]
    exact hb
  have hG₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 U ≫ G = (f ≫ u) ≫ q := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.equivalencePathFamilyPrism_endpoint]
    change (b ≫ pullback.snd q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v) ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) v) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0 = _
    rw [Category.assoc, Category.assoc, pullback.condition]
    change b₀ ≫ v = (f ≫ u) ≫ q
    rw [← s.fac_right, Category.assoc, ← h, Category.assoc]
  have hG₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 U ≫ G = b₁ ≫ q := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.equivalencePathFamilyPrism_endpoint]
    change (b ≫ pullback.snd q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v = (b ≫ pullback.fst q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v)) ≫ q
    simpa only [Category.assoc] using
      (congrArg (fun m : pullback q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v) ⟶ Y ↦ b ≫ m)
        (pullback.condition (f := q) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap v))).symm
  have hsf : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u v p q h ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) v =
        pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap q :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativePathSquareTargetMap_fst u v p q h 0
  have hPath : aPath ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap q = i ≫ bPath := by
    calc
      aPath ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap q = a ≫ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u v p q h ≫
          pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) v) := by
        dsimp only [aPath]
        rw [Category.assoc, hsf]
      _ = (a ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u v p q h) ≫
          pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) v := (Category.assoc _ _ _).symm
      _ = i ≫ bPath := by rw [ha]; simp only [bPath, Category.assoc]
  have hG : (Δ[1] ◁ i) ≫ G = H ≫ q := by
    apply curry_injective
    rw [curry_natural_left, curry_natural_right, curry_uncurry, curry_uncurry]
    calc
      i ≫ bPath ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y =
          (aPath ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y := by
        rw [hPath]
        simp only [bPath, Category.assoc]
      _ = (aPath ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) ≫ (ihom (Δ[1] : SSet.{u})).map q := by
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_ι, ← Category.assoc]
  obtain ⟨F, hF, hF₀, hF₁, hFq⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.exists_prism_extension_over_fixed_endpoints_of_lifting q i hq
      H (f ≫ u) b₁ G hH₀ hH₁ hG hG₀ hG₁
  have sl : CommSq aPath i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) (curry F) := by
    constructor
    rw [← curry_natural_left, hF, curry_uncurry]
  let L := sl.lift
  have hL : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X = curry F := sl.fac_right
  have hiL : i ≫ L = aPath := sl.fac_left
  have hL₀ : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0 = f ≫ u := by
    change L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = _
    rw [← Category.assoc, hL, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hF₀]
  have hL₁ : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 1 = b₁ := by
    change L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = _
    rw [← Category.assoc, hL, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hF₁]
  have hLq : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap q = bPath := by
    have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y) := by unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι; infer_instance
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y)).mp
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_ι, ← Category.assoc, hL,
      ← curry_natural_right, hFq, curry_uncurry]
  let R := pullback.lift L f hL₀
  have hRf : R ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) u = L := pullback.lift_fst _ _ _
  have hRs : R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection u = f := pullback.lift_snd _ _ _
  refine CommSq.HasLift.mk' { l := R, fac_left := ?_, fac_right := ?_ }
  · apply pullback.hom_ext
    · rw [Category.assoc, hRf]
      exact hiL
    · change (i ≫ R) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection u = a₀
      rw [Category.assoc, hRs]
      exact s.fac_left
  · apply pullback.hom_ext
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareEndCorner_fst]
      change R ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) u ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 1) = b₁
      rw [← Category.assoc, hRf, hL₁]
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareEndCorner_snd]
      apply pullback.hom_ext
      · rw [Category.assoc, hsf, ← Category.assoc, hRf, hLq]
        simp only [bPath, Category.assoc]
      · change (R ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap u v p q h) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection v = _
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareMap_projection, ← Category.assoc, hRs]
        exact s.fac_right

/-- 両縦射が inner fibration なら、終点比較は内 anodyne な射を持ち上げる。 -/
lemma hasLiftingProperty_replacementSquareEndCorner {A B X Y T U : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v)
    [InnerFibration p] [InnerFibration q] (i : T ⟶ U) (hi : innerAnodyneExtensions i) :
    HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareEndCorner u v p q h) := by
  have : HasLiftingProperty i p := hi _ (mem_innerFibrations _)
  have : HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) :=
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.hasLiftingProperty_fullSubcomplexOnVertices_ι_of_vertex_surjective
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex i (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.innerAnodyne_vertex_bijective i hi).surjective
  let r := Functor.PullbackObjObj.ofHasPullback internalHom (boundary 1).ι q
  have : InnerFibration r.π := innerFibration_pullbackObjObjπ r
  exact hasLiftingProperty_replacementSquareEndCorner_of_lifting u v p q h i
    (hi _ (mem_innerFibrations r.π))

/-- 両縦射の前合成同値の持ち上げは、終点比較にも伝わる。 -/
lemma kanEquivalenceLifting_replacementSquareEndCorner {A B X Y : SSet.{u}}
    [Quasicategory X] (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y)
    (h : u ≫ q = p ≫ v) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareEndCorner u v p q h) := by
  intro T U i hm hi
  have : Mono i := hm
  have := hp i hm hi
  have := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.kanEquivalenceLifting_equivalencePathι X i hm hi
  let r := Functor.PullbackObjObj.ofHasPullback internalHom (boundary 1).ι q
  exact hasLiftingProperty_replacementSquareEndCorner_of_lifting u v p q h i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.relativeInternalHom hq (boundary 1).ι r i hm hi)

/-- 両縦射が inner fibration の比較四角形の終点比較も inner fibration。 -/
instance replacementSquareEndCorner_innerFibration {A B X Y : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v)
    [InnerFibration p] [InnerFibration q] :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.replacementSquareEndCorner u v p q h) := by
  constructor
  intro T U i hi
  cases hi with
  | @intro n k h0 hn =>
    exact hasLiftingProperty_replacementSquareEndCorner u v p q h _
      (innerAnodyneExtensions.horn_ι h0 hn)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
