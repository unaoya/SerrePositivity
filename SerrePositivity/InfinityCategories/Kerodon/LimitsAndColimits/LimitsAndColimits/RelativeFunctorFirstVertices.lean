module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeInitialFirstVertices

/-!
概要：相対内部 Hom の始点境界充填を新しい単体の始点で判定する。
方針：相対内部 Hom の持ち上げを二つの指定部分を保つ図式の延長へ移す。
規約：全頂点での相対普遍性を仮定しない。
使われ方：境界を固定した関手の局所相対余極限の普遍性。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：指定部分の外の単体の始点での相対充填性は相対内部 Hom の充填性を与える。
方針：二成分を uncurry し、相対骨格で使う始点だけの条件で延長する。
規約：指定部分と射に fibration 性の仮定は置かない。
使われ方：境界パラメータを固定した余錐の局所普遍性の判定。 -/
lemma kanInitialBoundaryLifting_relativeFunctor_of_first_vertices {K X Y : SSet.{u}}
    (A : K.Subcomplex) (p : X ⟶ Y) (sq' : internalHom.PullbackObjObj A.ι p)
    (f : K ⟶ X)
    (hf : ∀ (m : ℕ) (s : K _⦋m + 1⦌), s ∉ A.obj (Opposite.op ⦋m + 1⦌) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p (f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting sq'.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
  intro n b β hb sq
  have hfst : b ≫ (pre A.ι).app X = (boundary (n + 1)).ι ≫ (β ≫ sq'.fst) := by
    have h := congrArg (fun q ↦ q ≫ sq'.fst) sq.w
    rw [Category.assoc, sq'.π_fst, Category.assoc] at h
    change b ≫ (pre A.ι).app X = (boundary (n + 1)).ι ≫ β ≫ sq'.fst at h
    exact h
  have hsnd : b ≫ (ihom K).map p = (boundary (n + 1)).ι ≫ (β ≫ sq'.snd) := by
    have h := congrArg (fun q ↦ q ≫ sq'.snd) sq.w
    rw [Category.assoc, sq'.π_snd, Category.assoc] at h
    change b ≫ (ihom K).map p = (boundary (n + 1)).ι ≫ β ≫ sq'.snd at h
    exact h
  have hba := congrArg uncurry hfst
  rw [uncurry_pre_app, uncurry_natural_left] at hba
  have hbp := congrArg uncurry hsnd
  rw [uncurry_natural_right, uncurry_natural_left] at hbp
  have htarget : (β ≫ sq'.fst) ≫ (ihom (A : SSet.{u})).map p =
      (β ≫ sq'.snd) ≫ (pre A.ι).app Y := by
    have h := congrArg (fun q ↦ β ≫ q) sq'.isPullback.w
    change β ≫ ((sq'.fst ≫ (ihom (A : SSet.{u})).map p)) =
      β ≫ (sq'.snd ≫ (pre A.ι).app Y) at h
    exact h
  have hap := congrArg uncurry htarget
  rw [uncurry_natural_right, uncurry_pre_app] at hap
  obtain ⟨F, hF, hFA, hFp⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanInitialBoundaryFamily_lift_of_relative_first_vertices p A n f b (uncurry (β ≫ sq'.fst))
      (uncurry (β ≫ sq'.snd)) hb hba hbp hap hf
  refine ⟨curry F, ?_, ?_⟩
  · apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    exact hF
  · apply sq'.hom_ext
    · rw [Category.assoc, sq'.π_fst]
      change curry F ≫ (pre A.ι).app X = β ≫ sq'.fst
      apply uncurry_injective
      rw [uncurry_pre_app, uncurry_curry]
      exact hFA
    · rw [Category.assoc, sq'.π_snd]
      change curry F ≫ (ihom K).map p = β ≫ sq'.snd
      apply uncurry_injective
      rw [uncurry_natural_right, uncurry_curry]
      exact hFp

/-- 概要：標準単体の境界を固定する相対内部 Hom は最初の頂点の条件だけで始点境界を充填する。
方針：境界外の単体は全頂点を通るので、その始点は標準の最初の頂点に一致する。
規約：他の頂点での普遍性を要求しない。
使われ方：Kerodon Proposition 7.1.8.7（Tag 06A5）、指定した境界を持つ局所余錐の普遍性。 -/
lemma kanInitialBoundaryLifting_relativeFunctor_boundary {X Y : SSet.{u}}
    (p : X ⟶ Y) (n : ℕ) (sq : internalHom.PullbackObjObj (boundary n).ι p)
    (f : (Δ[n] : SSet.{u}) ⟶ X)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p
      (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting sq.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
  apply kanInitialBoundaryLifting_relativeFunctor_of_first_vertices (boundary n) p sq f
  intro m s hs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorRelativeInitial.simplexFirstVertex_stdSimplex_of_notMem_boundary s hs]
  exact hf


end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
