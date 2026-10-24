module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeCoconeRestriction
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeConeFamilies

/-!
概要：相対余錐の局所充填から、指定部分と底を保つ余錐の族を延長する。
方針：相対余錐制限への持ち上げ問題を相対骨格で解き、uncurry で実際の図式へ戻す。
規約：指定部分は全頂点を含み、新しい単体の始点でのみ普遍性を要求する。
使われ方：Kerodon Proposition 7.1.8.7 の局所充填を相対 Kan の存在へ渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：図式と底の余錐を固定し、新しい単体の始点の相対充填性から余錐の族を延長する。
方針：二つの指定を引き戻しへ合わせ、相対骨格の持ち上げを具体的な図式へ戻す。
規約：元の射 U の fibration 性は不要。
使われ方：境界を固定する相対余錐の局所存在。 -/
lemma exists_kanRelativeCocone_extension_of_first_vertices {K D E B : SSet.{u}}
    (U : D ⟶ E) (A : B.Subcomplex)
    (hA : ∀ v : B _⦋0⦌, v ∈ A.obj (Opposite.op ⦋0⦌))
    (a : (A : SSet.{u}) ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj D)
    (d : B ⟶ (ihom K).obj D)
    (g : B ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj E)
    (h : d ≫ (ihom K).map U = g ≫ coconeRestriction K E)
    (ha : a ≫ coconeRestriction K D = A.ι ≫ d)
    (hg : a ≫ (ihom (join K (Δ[0] : SSet.{u}))).map U = A.ι ≫ g)
    (ht : ∀ (n : ℕ) (s : B _⦋n + 1⦌), s ∉ A.obj (Opposite.op ⦋n + 1⦌) →
      KanRelativeCoconeLifting U (kanCoconeFamilyAt a ⟨simplexFirstVertex s, hA _⟩)) :
    ∃ H : join K (Δ[0] : SSet.{u}) ⊗ B ⟶ D,
      (join K (Δ[0] : SSet.{u}) ◁ A.ι) ≫ H = uncurry a ∧
        (joinInl K (Δ[0] : SSet.{u}) ▷ B) ≫ H = uncurry d ∧ H ≫ U = uncurry g := by
  apply (kanRelativeCocone_lift_iff U A.ι a d g h).1
  apply exists_lift_of_initial_first_vertices A hA (kanRelativeCoconeRestriction K U) a
    (pullback.lift d g h)
  · apply pullback.hom_ext
    · rw [Category.assoc, kanRelativeCoconeRestriction_fst, Category.assoc, pullback.lift_fst]
      exact ha
    · rw [Category.assoc, kanRelativeCoconeRestriction_snd, Category.assoc, pullback.lift_snd]
      exact hg
  · intro n s hs
    have hx := ht n s hs
    dsimp only [KanRelativeCoconeLifting] at hx
    rwa [kanCoconeFamilyAt_vertex] at hx

/-- 概要：各点が相対余錐の充填条件を満たす族は、部分パラメータを固定しても相対始対象。
方針：各点の余錐と元の族の頂点の同定を相対内部 Hom の判定へ渡す。
規約：U とパラメータに fibration 性や quasicategory 性は要求しない。
使われ方：相対 Kan の局所普遍余錐の族の相対境界充填。 -/
lemma kanInitialBoundaryLifting_relativeCoconeFamily {J K D E : SSet.{u}}
    (U : D ⟶ E) (A : K.Subcomplex)
    (sq : internalHom.PullbackObjObj A.ι (kanRelativeCoconeRestriction J U))
    (f : K ⟶ (ihom (join J (Δ[0] : SSet.{u}))).obj D)
    (hf : ∀ k : K _⦋0⦌, KanRelativeCoconeLifting U (kanCoconeFamilyAt f k)) :
    InitialBoundaryLifting sq.π (functorVertex f) := by
  apply initialBoundaryLifting_relativeFunctor_of_pointwise A
    (kanRelativeCoconeRestriction J U) sq f
  intro k
  have h := hf k
  dsimp only [KanRelativeCoconeLifting] at h
  rwa [kanCoconeFamilyAt_vertex] at h

/-- 概要：自明 Kan fibration 上では全ての余錐が相対余錐の充填条件を満たす。
方針：相対余錐制限の全境界持ち上げを使う。
規約：余錐自体が絶対的な余極限であることは要求しない。
使われ方：相対条件と絶対条件の区別、および標的の同型の場合。 -/
lemma kanRelativeCoconeLifting_of_trivialKanFibration {K D E : SSet.{u}}
    (U : D ⟶ E) [TrivialKanFibration U] {p : K ⟶ D} (c : JoinCocone p) :
    KanRelativeCoconeLifting U c := by
  intro n a b _ sq
  have : HasLiftingProperty (boundary (n + 1)).ι (kanRelativeCoconeRestriction K U) :=
    TrivialKanFibration.mem (p := kanRelativeCoconeRestriction K U) _ inferInstance
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end SerrePositivity.InfinityCategories.F1B
