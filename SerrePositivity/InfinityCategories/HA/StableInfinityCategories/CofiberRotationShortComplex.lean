module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationConnecting
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberConnectingNaturality

/-! # 回転した二射列の cofiber 表示

概要：cofiber 列 A → B → C の B → C → ΣA は cofiber 列の像と同型である。
方針：回転長方形で最初の二射を同定し、最後の対象を構成済みの Σ へ移す。
規約：第三の接続射の負号はまだ主張しない。使われ方：TR2 の三対象・二射の整備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：短複体の二射が端点も含めて等しければ短複体全体が等しい。
方針：Arrow の等号から三対象と二射の等号に帰着し、零合成の証明の無関係性を使う。
規約：任意の零射を持つ圏。使われ方：幾何学的回転列の端点表示の照合。 -/
lemma shortComplex_eq_of_arrow_eq {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (S T : ShortComplex C) (hf : Arrow.mk S.f = Arrow.mk T.f)
    (hg : Arrow.mk S.g = Arrow.mk T.g) : S = T := by
  rcases S with @⟨A, B, D, f, g, hz⟩
  rcases T with @⟨A', B', D', f', g', hz'⟩
  obtain ⟨hA, hB, hfac⟩ := (Arrow.mk_eq_mk_iff f f').1 hf
  subst A'
  subst B'
  obtain ⟨_, hD, hgfac⟩ := (Arrow.mk_eq_mk_iff g g').1 hg
  subst D'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hfac hgfac
  subst f'
  subst g'
  rfl

/-- 概要：元の第二射と Σ への接続射は短複体を作る。
方針：接続射との零合成を使う。
規約：三対象は厳密に B・C・ΣA。使われ方：回転後の二射列の標準表示。 -/
def cofiberTailShortComplex {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) : ShortComplex (hoFunctor.obj X) :=
  ShortComplex.mk t.hoShortComplex.g (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting_comp_eq_zero t ht)

/-- 概要：元の第二射と指定 suspension への接続射の短複体は、回転後の列の像と等しい。
方針：回転後の二射と接続射の Arrow の等号を短複体の等号にまとめる。
規約：安定性は不要、入力に回転長方形を持つ。使われ方：標準 Σ への値域の輸送。 -/
lemma CofiberRotationRectangle.hoShortComplex_eq_tail {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X} (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationRectangle t) :
    r.rotatedZeroTriangle.hoShortComplex = ShortComplex.mk t.hoShortComplex.g
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht r.suspensionSquare)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension_comp_eq_zero t ht r.suspensionSquare) :=
  shortComplex_eq_of_arrow_eq _ _ r.rotated_f_arrow (r.rotated_g_arrow_connecting ht)

/-- 概要：回転列の短複体は B → C → ΣA と同型である。
方針：二射の等号で始点・中間対象を固定し、suspension 頂点の比較同型で最後を ΣA に移す。
規約：三角形の第三射の符号はこの同型に含まれない。使われ方：回転後の二射列の cofiber 表示。 -/
def CofiberRotationRectangle.tailShortComplexIso {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X} (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationRectangle t) :
    r.rotatedZeroTriangle.hoShortComplex ≅ cofiberTailShortComplex t ht := by
  let S := ShortComplex.mk t.hoShortComplex.g
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht r.suspensionSquare)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension_comp_eq_zero t ht r.suspensionSquare)
  let e : S ≅ cofiberTailShortComplex t ht := ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    r.suspensionSquare.suspensionFunctorObjIso.symm
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
    (by
      simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
      exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension_comp_objIso_inv t ht r.suspensionSquare).symm)
  exact eqToIso (r.hoShortComplex_eq_tail ht) ≪≫ e

/-- 概要：B → C → ΣA は、ある cofiber 列の短複体の像と同型である。
方針：回転長方形を選び、右側の列と標準 Σ への比較同型を取る。
規約：完全な三角形の回転の負号は別途証明する。使われ方：TR2 の二射列の存在部分。 -/
lemma exists_cofiberTailShortComplex {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence d ∧
      Nonempty (d.hoShortComplex ≅ cofiberTailShortComplex t ht) := by
  let r := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberRotationRectangle t ht
  exact ⟨r.rotatedZeroTriangle, r.rotated_isCofiber, ⟨r.tailShortComplexIso ht⟩⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
