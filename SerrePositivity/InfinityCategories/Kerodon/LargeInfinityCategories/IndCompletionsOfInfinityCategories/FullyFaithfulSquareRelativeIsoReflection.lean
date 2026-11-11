module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition
public import
  SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence
public import
  SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportSquareEndpointNormalization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra
/-!
概要：充満忠実な可換正方形で、同じ指定相対同型の射影の等号を反映する。
方針：同じ slice 同型の標準逆像を取り、後合成の可換性と充満忠実性を使う。
規約：比較の指定値と両端の全射を保持する。
使われ方：元の Ind diagram comma の始点評価下での相対反映。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：指定端点の等号による同型は、元の等号同型という性質を満たす。
方針：等号を消去する。規約：指定値を保持。使われ方：評価後の比較の反映。 -/
lemma isFunctorEqIso_eqToIso {A B : SSet.{u}} {f g : A ⟶ B} (h : f = g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (eqToIso (congrArg
      (fun v => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) h)) := by
  subst g
  exact ⟨rfl, rfl⟩

/-- 概要：指定同型の充満忠実な像が等号同型なら、元の指定端点の等号同型となる。
方針：像の同型の等式を反映する。規約：元の同型を保持。使われ方：相対反映。 -/
lemma fullyFaithful_reflects_functorEqIso {A B Y : SSet.{u}}
    [Quasicategory B] [Quasicategory Y] (k : B ⟶ Y) (hk : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful k)
    {f g : A ⟶ B} (h : f = g) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (e.postcomp k)) :
    e = eqToIso (congrArg (fun v => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) h) := by
  subst g
  apply hk.postcomp_functorIso_injective
  change e.postcomp k = (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f f from Iso.refl _).postcomp k
  have hr : (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f f from Iso.refl _).postcomp k =
      Iso.refl (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ k))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_eq_mapIso, Functor.mapIso_refl]
    rfl
  rw [hr]
  exact he.eq rfl
/-- 概要：slice 側で射影が等号となる同型の標準逆像も、指定射影で等号となる。
方針：可換正方形の両経路を照合する。規約：指定値を保持。使われ方：実 comma の反映。 -/
lemma fullyFaithful_preimage_functorIso_projection
    {A E X B Y : SSet.{u}}
    [Quasicategory E] [Quasicategory X] [Quasicategory B] [Quasicategory Y]
    (j : E ⟶ X) (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful j) (p : E ⟶ B)
    (q : X ⟶ Y) (k : B ⟶ Y) (hk : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful k)
    (hSquare : p ≫ k = j ≫ q) (f g : A ⟶ E) (hfg : f ≫ p = g ≫ p)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ j) (g ≫ j)) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (d.postcomp q)) :
    (hj.preimageFunctorIso d).postcomp p = eqToIso (congrArg
      (fun v => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) hfg) := by
  let d₀ := hj.preimageFunctorIso d
  have hd₀ : d₀.postcomp j = d := hj.preimageFunctorIso_postcomp d
  have hc : HEq ((d₀.postcomp p).postcomp k) (d.postcomp q) := by
    have hs : HEq (d₀.postcomp (p ≫ k)) (d₀.postcomp (j ≫ q)) := by rw [hSquare]
    exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp d₀ p k)).trans
      (hs.trans ((heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp d₀ j q).symm).trans
        (heq_of_eq (congrArg (fun t => t.postcomp q) hd₀))))
  have hs : (f ≫ j) ≫ q = (f ≫ p) ≫ k := by simp only [Category.assoc, hSquare]
  have ht : (g ≫ j) ≫ q = (g ≫ p) ≫ k := by simp only [Category.assoc, hSquare]
  exact fullyFaithful_reflects_functorEqIso k hk hfg (d₀.postcomp p)
    (hd.of_heq hs ht hc)
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
