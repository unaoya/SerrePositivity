module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.FiniteDiagramKanLifts
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.FiniteKanHomotopyDescent

/-! # Kan 置換後の有限図式の比較の反映

概要：有限対充填を持つ射の Kan 置換は、全ての有限パラメータでホモトピーを反映する。
方針：二図式と比較を共通有限部分へ下ろし、その部分図式の相対切断で比較を戻す。
規約：比較の存在を元の実 Kan ホモトピーへ戻す。使われ方：有限写像空間の全単射判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet

/-- 有限対充填を持つ射の Kan 置換は、有限パラメータの二図式の比較を反映する。 -/
lemma HasFiniteHomotopyRelativeFillers.kanFiniteDiagram_reflects_homotopy
    {E Q : SSet.{u}} {F : E ⟶ Q} (hF : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.HasFiniteHomotopyRelativeFillers F)
    {K : SSet.{u}} [K.Finite] (f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E)
    (H : SSet.Homotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map F)
      (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map F)) : Nonempty (SSet.Homotopy f g) := by
  obtain ⟨A, u₀, u₁, hu₀, hu₁⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.continuousKanFinitePair_factorization f g
  obtain ⟨B, t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finiteSubcomplex_factorization (A.val.ι ≫ F)
  let f₀ := u₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map t
  let f₁ := u₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map t
  have hv₀ : f₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map B.val.ι =
      f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map F := by
    dsimp only [f₀]
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, ht,
      CategoryTheory.Functor.map_comp, ← Category.assoc, hu₀]
  have hv₁ : f₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map B.val.ι =
      g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map F := by
    dsimp only [f₁]
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, ht,
      CategoryTheory.Functor.map_comp, ← Category.assoc, hu₁]
  let H₀ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget H hv₀.symm hv₁.symm
  obtain ⟨C, v, R, _⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.continuousKanFiniteHomotopy_descent B f₀ f₁ H₀
  let j := t ≫ Subcomplex.homOfLE (leOfHom v)
  have hj : A.val.ι ≫ F = j ≫ C.val.ι := by
    dsimp only [j]
    rw [Category.assoc, Subcomplex.homOfLE_ι]
    exact ht.symm
  obtain ⟨e, _, ⟨He⟩⟩ := hF.kanFiniteRelativeSection j A.val.ι C.val.ι hj
  let T : SSet.Homotopy (u₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map j)
      (u₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map j) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget R (by
        dsimp only [f₀, j]
        rw [CategoryTheory.Functor.map_comp, Category.assoc]) (by
        dsimp only [f₁, j]
        rw [CategoryTheory.Functor.map_comp, Category.assoc])
  have hm := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).2
    ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp T (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map e)⟩
  have h₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp He u₀⟩
  have h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp He u₁⟩
  simp only [CategoryTheory.Functor.map_comp, ← Category.assoc, hu₀] at h₀
  simp only [CategoryTheory.Functor.map_comp, ← Category.assoc, hu₁] at h₁
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).1 (h₀.symm.trans (hm.trans h₁))

/-- Kan 置換後の比較は、全ての有限パラメータの写像空間の連結成分上で単射。 -/
lemma HasFiniteHomotopyRelativeFillers.kanFiniteDiagramPiZero_injective
    {E Q : SSet.{u}} {F : E ⟶ Q} (hF : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.HasFiniteHomotopyRelativeFillers F)
    (K : SSet.{u}) [K.Finite] : Function.Injective
      (SSet.mapπ₀ ((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map F))) := by
  intro z w h
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective z
  obtain ⟨v', rfl⟩ := SSet.π₀.mk_surjective w
  obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E)).surjective v
  obtain ⟨g, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E)).surjective v'
  change SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map F)) =
    SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map F)) at h
  obtain ⟨H⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).1 h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).2
    (hF.kanFiniteDiagram_reflects_homotopy f g H)

/-- Kan 置換後の比較は、全ての有限パラメータの写像空間の連結成分上で全単射。 -/
lemma HasFiniteHomotopyRelativeFillers.kanFiniteDiagramPiZero_bijective
    {E Q : SSet.{u}} {F : E ⟶ Q} (hF : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.HasFiniteHomotopyRelativeFillers F)
    (K : SSet.{u}) [K.Finite] : Function.Bijective
      (SSet.mapπ₀ ((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map F))) :=
  ⟨hF.kanFiniteDiagramPiZero_injective K, hF.kanFiniteDiagramPiZero_surjective K⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
