module

public import SerrePositivity.KST.Comparison.FibrationLocality
public import SerrePositivity.KST.Comparison.CoproductPullbacks
public import SerrePositivity.KST.Comparison.CartesianTensorSquare

/-!
# 積と余積による Kan fibration の保存

概要：固定対象との直積と二項余積の射は Kan fibration を保つ。
方針：直積は引き戻しとして、余積は厳密な包含の引き戻しと単体ごとの局所性で扱う。
規約：Segal 1974 Lemma 1.7 の厳密な円筒の比較への補助。
使われ方：二重写像円筒の中央の円筒と端点の余積の Kan 条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

/--
概要：固定した右因子との直積の射と第一射影の正方形は厳密な引き戻しである。
方針：各次数で一致する第一成分と右因子の成分から元の組を復元する。
規約：基底の Kan 性を使わない直積の普遍性。
使われ方：固定対象との直積が Kan fibration を保つこと。
-/
theorem tensorRight_fst_isPullback {X Y : SSet.{u}} (f : X ⟶ Y) (T : SSet.{u}) :
    IsPullback (fst X T) (f ▷ T) f (fst Y T) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨x, t⟩ ⟨y, u⟩ ⟨h₁, h₂⟩
    change x = y at h₁
    change (f.app d x, t) = (f.app d y, u) at h₂
    exact Prod.ext h₁ (congrArg (fun p : Y.obj d × T.obj d => p.2) h₂)
  · rintro x ⟨y, t⟩ h
    change f.app d x = y at h
    exact ⟨(x, t), rfl, Prod.ext h rfl⟩

/--
概要：任意の固定対象との右側の直積は Kan fibration を保つ。
方針：第一射影の引き戻しとして右持ち上げ性を移す。
規約：固定対象の Kan 性は不要。
使われ方：円筒の中央の射 c⊗id の Kan 条件。
-/
theorem tensorRight_rlp {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.modelCategoryQuillen.J.rlp f) (T : SSet.{u}) :
    SSet.modelCategoryQuillen.J.rlp (f ▷ T) :=
  SSet.modelCategoryQuillen.J.rlp.of_isPullback (tensorRight_fst_isPullback f T) hf

/--
概要：二つの Kan fibration の二項余積は Kan fibration である。
方針：余積の包含の引き戻しと、始対象からの pushout の単体ごとの局所性を使う。
規約：各基底の Kan 性や連結性を要求しない。
使われ方：二重写像円筒の端点の余積の射。
-/
theorem coproductMap_rlp {A B A' B' : SSet.{u}} (a : A ⟶ A') (b : B ⟶ B')
    (ha : SSet.modelCategoryQuillen.J.rlp a) (hb : SSet.modelCategoryQuillen.J.rlp b) :
    SSet.modelCategoryQuillen.J.rlp (coprod.map a b) :=
  kanFibration_of_pushoutCover (IsPushout.of_hasBinaryCoproduct' A' B') (coprod.map a b)
    a coprod.inl (coproductInclusions_isPullback a b).1
    b coprod.inr (coproductInclusions_isPullback a b).2 ha hb

end SerrePositivity.KST.Comparison
