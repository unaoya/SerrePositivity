module

public import SerrePositivity.InfinityCategories.F2.Presentable.OppositeAdjointExistence
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallContravariantHomContinuity
public import SerrePositivity.InfinityCategories.F2.Presentable.LeftAdjointAllColimitPreservation

/-!
概要：小さい連続前層の表現可能性を右随伴の存在へ接続する。
方針：標的の小さい反変 Hom を前合成し、得た表現対象を全随伴へ組み立てる。
規約：一般の表現可能性と宇宙変更の反映は明示入力で、ここではその存在を主張しない。
使われ方：d2 と Compact の反映界面を d4 の判定へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：連続前層の表現定理と反映界面の下で余極限保存関手の右随伴を構成する。
方針：各小さい反変 Hom 合成を表現し、全自然比較から反対圏の随伴を戻す。
規約：入力の表現定理は元の始域上の全ての小さい空間値連続前層を対象とする。
使われ方：d4 の存在方向の接続。 -/
lemma exists_rightAdjoint_of_colimitPreserving_representability
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
    (hU : IsFullyFaithful Compact.spaceUniverseDiagram.{u}) (hY : IsAccessible Y)
    (hRep : ∀ H : X.op ⟶ SpaceInfinity.{u}, SendsSmallColimitsToLimits H →
      IsRepresentableSmallSpaceFunctor H) (L : X ⟶ Y) (hL : PreservesSmallColimits L) :
    ∃ R : Y ⟶ X, Nonempty (QCatAdjunction L R) := by
  apply exists_rightAdjoint_of_contravariantHom_representable L
  intro y
  obtain ⟨H, ⟨hH⟩⟩ := hY.exists_smallContravariantHom y
  obtain ⟨x, ⟨hx⟩⟩ := hRep (SSet.opFunctor.map L ≫ H)
    (smallContravariantHomComposite_sendsSmallColimitsToLimits hU L hL y H hH)
  refine ⟨x, ⟨hx ≪≫ ?_⟩⟩
  have h := FunctorIso.precomp hH
    ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map L))
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using h.symm

/-- 概要：反映界面と連続前層の表現定理の下で右随伴の存在は小余極限保存と同値。
方針：存在方向を小さい Hom 模型で構成し、必要方向は全随伴の余極限保存を使う。
規約：一般の d2 および反映界面を明示し、無条件の随伴関手定理とは区別する。
使われ方：二つの供給界面を得た後の d4 の公開判定への接続。 -/
lemma exists_rightAdjoint_iff_preservesSmallColimits_of_representability
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
    (hU : IsFullyFaithful Compact.spaceUniverseDiagram.{u}) (hY : IsAccessible Y)
    (hRep : ∀ H : X.op ⟶ SpaceInfinity.{u}, SendsSmallColimitsToLimits H →
      IsRepresentableSmallSpaceFunctor H) (L : X ⟶ Y) :
    (∃ R : Y ⟶ X, Nonempty (QCatAdjunction L R)) ↔ PreservesSmallColimits L := by
  constructor
  · rintro ⟨R, ⟨a⟩⟩
    exact adjunction_preservesSmallColimits a
  · exact exists_rightAdjoint_of_colimitPreserving_representability hU hY hRep L

end SerrePositivity.InfinityCategories.F2.Presentable
