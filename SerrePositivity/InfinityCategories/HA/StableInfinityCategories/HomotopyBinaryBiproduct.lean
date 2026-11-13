module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SplitCofiberProduct
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroSourceCofiberComparison
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-! # 安定 ∞ 圏のホモトピー圏の二項双積

概要：零始点の押し出しの標準射影は二項積となり、h C は二項双積を持つ。
方針：標準包含の cofiber 列へ指定左逆を移し、分裂 cofiber 列の積性を使う。
規約：前加法構造を仮定しない。使われ方：h C の加法構造と三角構造。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：二射列の Arrow の等号は、全ての左逆での積性を輸送する。
方針：Arrow の等号から三対象と二射の等号へ帰着する。
規約：任意の圏で成り立つ。使われ方：幾何学的 cofiber 列の端点の表示の変更。 -/
def binaryProductOfRetraction_of_arrow_eq {C : Type u} [Category.{v} C]
    {A B D A' B' D' : C} {f : A ⟶ B} {g : B ⟶ D}
    {f' : A' ⟶ B'} {g' : B' ⟶ D'}
    (hp : ∀ (r : B ⟶ A), f ≫ r = 𝟙 A → IsLimit (BinaryFan.mk r g))
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g')
    (r : B' ⟶ A') (hr : f' ≫ r = 𝟙 A') : IsLimit (BinaryFan.mk r g') := by
  apply Classical.choice
  obtain ⟨hA, hB, hf⟩ := (Arrow.mk_eq_mk_iff f f').1 hf
  subst A'
  subst B'
  obtain ⟨_, hD, hg⟩ := (Arrow.mk_eq_mk_iff g g').1 hg
  subst D'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  subst f'
  subst g'
  exact ⟨hp r hr⟩

/-- 概要：第一包含の任意の左逆と標準第二射影は二項積を与える。
方針：第一包含と第二射影の cofiber 列に、指定された左逆を移す。
規約：前加法構造は使わない。使われ方：標準射影の積性と射の加法逆元の構成。 -/
def zeroSourcePushout_isBinaryProduct_of_retraction {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 0 0))
    (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex R 1 1 ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex R 1 0)
    (hr : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight R ≫ r = 𝟙 _) :
    IsLimit (BinaryFan.mk r (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproductSnd R hR hz.1)) := by
  apply Classical.choice
  obtain ⟨t, ht, hf, hg, _⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_coproductCofiberSequence R hR hz
  exact ⟨binaryProductOfRetraction_of_arrow_eq
    (fun r hr => t.binaryProductOfRetraction ht r hr) hf hg r hr⟩

/-- 概要：零始点の押し出しの二つの標準射影は二項積を与える。
方針：標準第一射影を左逆として前補題に指定する。
規約：安定性を仮定し、前加法構造は使わない。使われ方：二項双積の普遍性。 -/
def zeroSourcePushout_isBinaryProduct {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 0 0)) :
    IsLimit (BinaryFan.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproductFst R hR hz.1)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproductSnd R hR hz.1)) :=
  zeroSourcePushout_isBinaryProduct_of_retraction R hR hz _
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproduct_right_fst R hR hz.1)

/-- 概要：零始点の押し出しは標準包含・射影を持つ二項双積データとなる。
方針：四つの合成式に積と余積の二つの普遍性を組み合わせる。
規約：双積の頂点は元の四角形の終端頂点。使われ方：h C の二項双積 instance。 -/
def zeroSourcePushoutBinaryBiproduct {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 0 0)) :
    BinaryBiproductData (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex R 1 0) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex R 0 1) where
  bicone :=
    { pt := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex R 1 1
      fst := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproductFst R hR hz.1
      snd := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproductSnd R hR hz.1
      inl := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight R
      inr := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoTop R
      inl_fst := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproduct_right_fst R hR hz.1
      inl_snd := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproduct_right_snd R hR hz.1
      inr_fst := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproduct_top_fst R hR hz.1
      inr_snd := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproduct_top_snd R hR hz.1 }
  isBilimit :=
    { isLimit := zeroSourcePushout_isBinaryProduct R hR hz
      isColimit := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourcePushout_isBinaryCoproduct R hR hz.1 }

/-- 概要：安定 ∞ 圏のホモトピー圏は二項双積を持つ。
方針：二対象を頂点で表し、指定二頂点の零始点押し出しから双積を得る。
規約：前加法構造は仮定しない。使われ方：三角圏の加法構造の構成。 -/
instance hasBinaryBiproducts_ho {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    HasBinaryBiproducts (hoFunctor.obj X) where
  has_binary_biproduct a b := by
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
    obtain ⟨R, hz, hx, hy, hR⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_zeroSourcePushoutSquare x y
    have h := HasBinaryBiproduct.mk (zeroSourcePushoutBinaryBiproduct R hR hz)
    change HasBinaryBiproduct (C := hoFunctor.obj X)
      (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 1 0))
      (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 0 1)) at h
    rw [hx, hy] at h
    exact h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.1.3.5" (partial := component) "仮定：安定準圏と二対象（HA と一致）。結論：有限積・余積の存在と、零始点の押し出しから hX の双積を作る。∞ 圏の正方形自体から余積→積の標準同値を比較する宣言は採用した型にない（Lean が弱い）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourcePushoutBinaryBiproduct
attribute [cite HA "1.4.1.3" (partial := component) "仮定：安定準圏（Lean が弱い：presentable 性は不要）。結論：ホモトピー圏の前加法性と双積があり、原典冒頭の加法性に対応する（Lean が弱い：各対象の余群構造と compactly generated な場合の Brown の全仮定の確認は含まれない）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasBinaryBiproducts_ho
