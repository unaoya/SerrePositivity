module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinRelativeInitialBoundary
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.RelativeInitialExtension

/-!
概要：局所の相対余錐条件から変動する添字の関手の族を相対的に組み立てる。
方針：全空間の相対始点境界充填を、全頂点を含む部分複体の相対骨格に適用する。
規約：元の図式の族と標的での全図式の族を同時に固定する。
使われ方：境界を固定した関手圏上の相対 Kan 拡張の存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：各始点の相対普遍余錐から、元の図式と標的の全図式を保つ族の延長が存在する。
方針：二つの指定を引き戻しへ合わせ、局所から全空間への移送と相対骨格の充填を使う。
規約：相対条件は欠けた正次元単体の最初の頂点だけに要求する。
使われ方：全頂点を含む部分上の相対 Kan 拡張を全体へ組み立てる。 -/
lemma exists_kanRelativeJoin_relativeFamily_extension {K C P Q X A : SSet.{u}}
    [Quasicategory C] [Quasicategory X] (p : K ⟶ C) [CocartesianFibration p]
    (v : P ⟶ Q) [Mono v] (A₀ : A.Subcomplex)
    (hA₀ : ∀ x : A _⦋0⦌, x ∈ A₀.obj (Opposite.op ⦋0⦌))
    (a : (A₀ : SSet.{u}) ⟶ SerrePositivity.InfinityCategories.fiberwiseHom (relativeJoinBaseProjection p (𝟙 C)) ((ihom Q).obj X))
    (b₀ : A ⟶ SerrePositivity.InfinityCategories.fiberwiseHom p ((ihom Q).obj X))
    (b₁ : A ⟶ SerrePositivity.InfinityCategories.fiberwiseHom (relativeJoinBaseProjection p (𝟙 C)) ((ihom P).obj X))
    (hcompat : b₀ ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp p ((pre v).app X) =
      b₁ ≫ SerrePositivity.InfinityCategories.fiberwiseHomPre (D := (ihom P).obj X) (kanRelativeJoinInlOver p))
    (ha₀ : a ≫ SerrePositivity.InfinityCategories.fiberwiseHomPre (D := (ihom Q).obj X) (kanRelativeJoinInlOver p) = A₀.ι ≫ b₀)
    (ha₁ : a ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp (relativeJoinBaseProjection p (𝟙 C)) ((pre v).app X) =
      A₀.ι ≫ b₁)
    (hlocal : ∀ (n : ℕ) (σ : A _⦋n + 1⦌), σ ∉ A₀.obj (Opposite.op ⦋n + 1⦌) →
      ∃ (c : C _⦋0⦌) (d : vertexFiber p c ⟶ (ihom Q).obj X) (z : JoinCocone d),
        KanRelativeCoconeLifting ((pre v).app X) z ∧
        (((kanRelativeJoinCoconeFiberIso p c ((ihom Q).obj X)).hom.app (Opposite.op ⦋0⦌)
          (functorVertex z.val)).val) = a.app (Opposite.op ⦋0⦌) ⟨simplexFirstVertex σ, hA₀ _⟩) :
    ∃ l : A ⟶ SerrePositivity.InfinityCategories.fiberwiseHom (relativeJoinBaseProjection p (𝟙 C)) ((ihom Q).obj X),
      A₀.ι ≫ l = a ∧
        l ≫ SerrePositivity.InfinityCategories.fiberwiseHomPre (D := (ihom Q).obj X) (kanRelativeJoinInlOver p) = b₀ ∧
        l ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp (relativeJoinBaseProjection p (𝟙 C)) ((pre v).app X) = b₁ := by
  let b := pullback.lift b₀ b₁ hcompat
  have hw : a ≫ SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction (kanRelativeJoinInlOver p) ((pre v).app X) =
      A₀.ι ≫ b := by
    dsimp only [b]
    apply pullback.hom_ext
    · erw [Category.assoc, SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction_fst, Category.assoc, pullback.lift_fst]
      exact ha₀
    · erw [Category.assoc, SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction_snd, Category.assoc, pullback.lift_snd]
      exact ha₁
  have hinit : ∀ (n : ℕ) (σ : A _⦋n + 1⦌), σ ∉ A₀.obj (Opposite.op ⦋n + 1⦌) →
      InitialBoundaryLifting
        (SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction (kanRelativeJoinInlOver p) ((pre v).app X))
        (a.app (Opposite.op ⦋0⦌) ⟨simplexFirstVertex σ, hA₀ _⟩) := by
    intro n σ hσ
    obtain ⟨c, d, z, hz, he⟩ := hlocal n σ hσ
    exact he ▸ kanRelativeJoinRelative_initialBoundary_of_local p v c hz
  obtain ⟨l, hla, hlb⟩ := exists_lift_of_initial_first_vertices A₀ hA₀
    (SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction (kanRelativeJoinInlOver p) ((pre v).app X)) a b hw hinit
  refine ⟨l, hla, ?_, ?_⟩
  · have h := congrArg (fun z ↦ z ≫ pullback.fst (SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp p ((pre v).app X))
      (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := (ihom P).obj X) (kanRelativeJoinInlOver p))) hlb
    simp only [b, Category.assoc] at h
    erw [SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction_fst, pullback.lift_fst] at h
    exact h
  · have h := congrArg (fun z ↦ z ≫ pullback.snd (SerrePositivity.InfinityCategories.F1B.fiberwiseHomPostcomp p ((pre v).app X))
      (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := (ihom P).obj X) (kanRelativeJoinInlOver p))) hlb
    simp only [b, Category.assoc] at h
    erw [SerrePositivity.InfinityCategories.F1B.fiberwiseRelativeRestriction_snd, pullback.lift_snd] at h
    exact h

end SerrePositivity.InfinityCategories.F1B
