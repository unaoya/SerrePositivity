module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.PairingInner
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseKanExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal

/-!
概要：twisted arrow の左ホーンの延長領域から quasicategory への延長を構成する。
方針：inner anodyne な包含で終対象への射を持ち上げ、重みの標準同型で戻す。
規約：指定された部分領域上で元の図式と厳密に一致する。
使われ方：実際のホーンの各面と左右の半分を接合した後の充填の存在。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 左ホーンの標準単体内の固定領域上の図式は、任意の quasicategory で延長できる。 -/
lemma exists_twistedArrowExtensionDomain_extension {C : SSet.{u}} [Quasicategory C]
    {n : ℕ} (i : Fin (n + 1)) (hi : i < Fin.last n)
    (f : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionDomain n i : SSet.{u}) ⟶ C) :
    ∃ F : (Δ[n + n + 1] : SSet.{u}) ⟶ C, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionDomain n i).ι ≫ F = f := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionDomain_innerAnodyne i hi (terminal.from C)
    (InnerFibration.mem (q := terminal.from C))
  have sq : CommSq f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionDomain n i).ι (terminal.from C)
      (terminal.from (Δ[n + n + 1] : SSet.{u})) := ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 同じ左ホーンの固定領域を元の join の重みの中に取る。 -/
def twistedArrowWeightDomain (n : ℕ) (i : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.obj ⦋n⦌).Subcomplex :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionDomain n i).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso n).hom

/-- 実際の join の重みでも、固定領域上の図式を厳密に保つ延長が存在する。 -/
lemma exists_twistedArrowWeightDomain_extension {C : SSet.{u}} [Quasicategory C]
    {n : ℕ} (i : Fin (n + 1)) (hi : i < Fin.last n)
    (f : (twistedArrowWeightDomain n i : SSet.{u}) ⟶ C) :
    ∃ F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n⦌ ⟶ C, (twistedArrowWeightDomain n i).ι ≫ F = f := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.subcomplexPreimageIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionDomain n i) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso n)
  obtain ⟨F, hF⟩ := exists_twistedArrowExtensionDomain_extension i hi (e.inv ≫ f)
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso n).hom ≫ F, ?_⟩
  calc
    _ = e.hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowExtensionDomain n i).ι ≫ F := by rfl
    _ = e.hom ≫ e.inv ≫ f := by rw [hF]
    _ = f := by rw [← Category.assoc, e.hom_inv_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
