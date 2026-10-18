module

public import SerrePositivity.KST.Comparison.TensorSubcomplexGluing
public import SerrePositivity.KST.Comparison.HomotopyPullbackSymmetry

/-!
# 空の部分単体集合でのファイバー比較

概要：右因子を空の部分単体集合へ制限した四角形は、常にホモトピー引き戻しである。
方針：固定射を Kan 分解し、空の対象の厳密な引き戻しの普遍性を各次数で確認する。
規約：Segal 1974 Proposition 1.6 の有限被覆の帰納の空の場合。
使われ方：有限交叉から有限和へ進む束の帰納の基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.SimplicialModel

/--
概要：右因子を空に制限した四角形はホモトピー引き戻しである。
方針：別分解の比較先の厳密ファイバーも空であり、比較は普遍性の同型となる。
規約：固定射や元の四角形に追加条件を課さない。
使われ方：標準単体の境界の面の有限被覆の空の場合。
-/
theorem tensorSubcomplex_homotopyPullback_bot
    {X' X K T' T : SSet.{u}} {f : X' ⟶ X}
    {a : X' ⊗ K ⟶ T'} {p : T' ⟶ T} {b : X ⊗ K ⟶ T}
    (sq : CommSq a (f ▷ K) p b) :
    IsHomotopyPullback (tensorSubcomplexSquare sq ⊥) := by
  let dp := AnodyneKanReplacement.factorization.factorizationData p
  let s := tensorSubcomplexSquare sq ⊥
  have hw : (f ▷ (⊥ : K.Subcomplex).toSSet) ≫ ((X ◁ (⊥ : K.Subcomplex).ι) ≫ b) =
      (((X' ◁ (⊥ : K.Subcomplex).ι) ≫ a) ≫ dp.i) ≫ dp.p := by
    rw [Category.assoc, dp.fac]
    exact s.w.symm
  have hp : IsPullback (f ▷ (⊥ : K.Subcomplex).toSSet)
      (((X' ◁ (⊥ : K.Subcomplex).ι) ≫ a) ≫ dp.i)
      ((X ◁ (⊥ : K.Subcomplex).ι) ≫ b) dp.p := by
    apply IsPullback.of_forall_isPullback_app
    intro d
    apply (Types.isPullback_iff _ _ _ _).mpr
    refine ⟨congrArg (fun t => t.app d) hw, ?_, ?_⟩
    · rintro ⟨x, z⟩ _ _
      exact False.elim z.2
    · rintro ⟨x, z⟩ _ _
      exact False.elim z.2
  apply (isHomotopyPullback_flip_iff s).mp
  apply (isHomotopyPullback_iff_alternative s.flip dp.i dp.hi dp.p dp.hp dp.fac).mpr
  exact inferInstanceAs (IsIso (AnodyneHomotopy.anodyneQ.map hp.isoPullback.hom))

end SerrePositivity.KST.Comparison
