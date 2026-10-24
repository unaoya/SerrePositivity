module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeFunctorFirstVertices
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeCoconeTerminal
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeConeFamilies

/-!
概要：境界を固定した余錐の族の相対普遍性を最初の余錐で判定する。
方針：相対余錐制限へ相対内部 Hom の始点判定を適用する。
規約：他のパラメータ頂点での普遍性は要求しない。
使われ方：Kan 拡張の写像空間の制限定理で用いる局所余錐の境界充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：最初の相対余錐が普遍なら、境界を固定した余錐の族は相対始点境界を充填する。
方針：標準単体の相対内部 Hom の判定と、余錐の族の頂点の式を使う。
規約：U と値域に追加の充填性の仮定は不要。
使われ方：境界を固定する関手 V′ の局所相対余極限の普遍性の入力。 -/
lemma kanInitialBoundaryLifting_relativeCoconeFamily_boundary {J D E : SSet.{u}}
    (U : D ⟶ E) (n : ℕ)
    (sq : internalHom.PullbackObjObj (boundary n).ι (kanRelativeCoconeRestriction J U))
    (f : (Δ[n] : SSet.{u}) ⟶ (ihom (join J (Δ[0] : SSet.{u}))).obj D)
    (hf : KanRelativeCoconeLifting U
      (kanCoconeFamilyAt f (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))) :
    InitialBoundaryLifting sq.π (functorVertex f) := by
  apply kanInitialBoundaryLifting_relativeFunctor_boundary (kanRelativeCoconeRestriction J U) n sq f
  have h := hf
  dsimp only [KanRelativeCoconeLifting] at h
  rwa [kanCoconeFamilyAt_vertex] at h

/-- 概要：絶対的に普遍な最初の余錐から、終対象上で境界を固定した族の相対充填性を得る。
方針：終対象上の相対余錐条件を通常の余極限性に同定して始点判定に渡す。
規約：D の quasicategory 性のみを仮定する。
使われ方：通常の Kan 条件から写像空間の制限の境界充填へ進む局所入力。 -/
lemma kanInitialBoundaryLifting_relativeCoconeFamily_boundary_of_colimit {J D E : SSet.{u}}
    [Quasicategory D] (U : D ⟶ E) (hE : CategoryTheory.Limits.IsTerminal E) (n : ℕ)
    (sq : internalHom.PullbackObjObj (boundary n).ι (kanRelativeCoconeRestriction J U))
    (f : (Δ[n] : SSet.{u}) ⟶ (ihom (join J (Δ[0] : SSet.{u}))).obj D)
    (hf : IsColimitCone
      (kanCoconeFamilyAt f (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))) :
    InitialBoundaryLifting sq.π (functorVertex f) := by
  apply kanInitialBoundaryLifting_relativeCoconeFamily_boundary U n sq f
  exact (kanRelativeCoconeLifting_iff_isColimit_of_terminal U hE _).2 hf

end SerrePositivity.InfinityCategories.F1B
