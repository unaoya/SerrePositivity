module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NormalizedHomNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.StraighteningBaseChangeRestriction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentPost

/-!
概要：指定成分の正規化と内部Homの制限の整合性。
方針：既存の成分の後合成の法則へ戻し、同じ端点移送を消去する。
規約：元の関手同型と元の成分を保持する。
使われ方：Kerodon §9.5（Tag 06NC）で使う関手空間の成分計算、分類底変換の初頂点制限。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open Project.LocalizationAndKanExtensionAuxiliaries
open Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
namespace PresentableInfinityCategories

/-- 概要：指定成分の頂点による正規化は元の成分の端点移送だけを変える。
方針：元の両等式を消去する。規約：同じ成分自身の異種等式。
使われ方：内部Homの制限と指定成分の整合性の証明分割。 -/
lemma normalizedFunctorIsoComponent_heq_app {I Y : SSet.{u}}
    [Quasicategory I] [Quasicategory Y] {F G : I ⟶ Y}
    (e : FunctorIso F G) (x : I _⦋0⦌) {xf xg : Y _⦋0⦌}
    (hf : xf = F.app (Opposite.op ⦋0⦌) x) (hg : xg = G.app (Opposite.op ⦋0⦌) x) :
    HEq (normalizedFunctorIsoComponent e x hf hg) (e.app x) := by
  subst xf
  subst xg
  simp only [normalizedFunctorIsoComponent, eqToIso_refl, Iso.refl_trans,
    Iso.refl_symm, Iso.trans_refl]
  rfl

/-- 概要：指定した図式値同型の正規化した成分を制限すると、制限後の同じ成分になる。
方針：成分の後合成の既存法則と、同じ内部前合成の像の法則を使う。
規約：元の同型・点・端点表示を保持する。使われ方：指定底変換の初頂点制限の照合。 -/
lemma normalizedFunctorIsoComponent_precomp_heq {I A B X : SSet.{u}}
    [Quasicategory I] [Quasicategory X] {F G : I ⟶ (ihom A).obj X}
    (e : FunctorIso F G) (x : I _⦋0⦌) {f g : A ⟶ X}
    (hf : functorVertex f = F.app (Opposite.op ⦋0⦌) x)
    (hg : functorVertex g = G.app (Opposite.op ⦋0⦌) x) (q : B ⟶ A) :
    HEq ((show FunctorIso f g from normalizedFunctorIsoComponent e x hf hg).precomp q)
      ((e.postcomp ((pre q).app X)).app x) := by
  have hn := normalizedFunctorIsoComponent_heq_app e x hf hg
  have hm := vertexIso_map_heq_of_heq (normalizedFunctorIsoComponent e x hf hg)
    (e.app x) hf hg hn ((pre q).app X)
  have hp := functorIsoPrecomp_heq_map
    (show FunctorIso f g from normalizedFunctorIsoComponent e x hf hg) q
  exact hp.trans (hm.trans (functorIso_app_postcomp_heq e ((pre q).app X) x).symm)

end PresentableInfinityCategories
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
