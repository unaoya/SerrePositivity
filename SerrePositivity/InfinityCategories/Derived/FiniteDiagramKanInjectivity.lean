module
public import SerrePositivity.InfinityCategories.Derived.FiniteDiagramKanLifts
public import SerrePositivity.InfinityCategories.Derived.FiniteKanHomotopyDescent

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet F2

/-- 有限対充填を持つ射の Kan 置換は、有限パラメータの二図式の比較を反映する。 -/
lemma HasFiniteHomotopyRelativeFillers.kanFiniteDiagram_reflects_homotopy
    {E Q : SSet.{u}} {F : E ⟶ Q} (hF : HasFiniteHomotopyRelativeFillers F)
    {K : SSet.{u}} [K.Finite] (f g : K ⟶ continuousKanReplacement.obj E)
    (H : SSet.Homotopy (f ≫ continuousKanReplacement.map F)
      (g ≫ continuousKanReplacement.map F)) : Nonempty (SSet.Homotopy f g) := by
  obtain ⟨A, u₀, u₁, hu₀, hu₁⟩ := continuousKanFinitePair_factorization f g
  obtain ⟨B, t, ht⟩ := finiteSubcomplex_factorization (A.val.ι ≫ F)
  let f₀ := u₀ ≫ continuousKanReplacement.map t
  let f₁ := u₁ ≫ continuousKanReplacement.map t
  have hv₀ : f₀ ≫ continuousKanReplacement.map B.val.ι =
      f ≫ continuousKanReplacement.map F := by
    dsimp only [f₀]
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, ht,
      CategoryTheory.Functor.map_comp, ← Category.assoc, hu₀]
  have hv₁ : f₁ ≫ continuousKanReplacement.map B.val.ι =
      g ≫ continuousKanReplacement.map F := by
    dsimp only [f₁]
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, ht,
      CategoryTheory.Functor.map_comp, ← Category.assoc, hu₁]
  let H₀ := stableHomotopyRetarget H hv₀.symm hv₁.symm
  obtain ⟨C, v, R, _⟩ := continuousKanFiniteHomotopy_descent B f₀ f₁ H₀
  let j := t ≫ Subcomplex.homOfLE (leOfHom v)
  have hj : A.val.ι ≫ F = j ≫ C.val.ι := by
    dsimp only [j]
    rw [Category.assoc, Subcomplex.homOfLE_ι]
    exact ht.symm
  obtain ⟨e, _, ⟨He⟩⟩ := hF.kanFiniteRelativeSection j A.val.ι C.val.ι hj
  let T : SSet.Homotopy (u₀ ≫ continuousKanReplacement.map j)
      (u₁ ≫ continuousKanReplacement.map j) := stableHomotopyRetarget R (by
        dsimp only [f₀, j]
        rw [CategoryTheory.Functor.map_comp, Category.assoc]) (by
        dsimp only [f₁, j]
        rw [CategoryTheory.Functor.map_comp, Category.assoc])
  have hm := (functorVertex_piZero_eq_iff_homotopy _ _).2
    ⟨functorHomotopyPostcomp T (continuousKanReplacement.map e)⟩
  have h₀ := (functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨functorHomotopyPrecomp He u₀⟩
  have h₁ := (functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨functorHomotopyPrecomp He u₁⟩
  simp only [CategoryTheory.Functor.map_comp, ← Category.assoc, hu₀] at h₀
  simp only [CategoryTheory.Functor.map_comp, ← Category.assoc, hu₁] at h₁
  exact (functorVertex_piZero_eq_iff_homotopy _ _).1 (h₀.symm.trans (hm.trans h₁))

/-- Kan 置換後の比較は、全ての有限パラメータの写像空間の連結成分上で単射。 -/
lemma HasFiniteHomotopyRelativeFillers.kanFiniteDiagramPiZero_injective
    {E Q : SSet.{u}} {F : E ⟶ Q} (hF : HasFiniteHomotopyRelativeFillers F)
    (K : SSet.{u}) [K.Finite] : Function.Injective
      (SSet.mapπ₀ ((ihom K).map (continuousKanReplacement.map F))) := by
  intro z w h
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective z
  obtain ⟨v', rfl⟩ := SSet.π₀.mk_surjective w
  obtain ⟨f, rfl⟩ := (functorVertexEquiv K (continuousKanReplacement.obj E)).surjective v
  obtain ⟨g, rfl⟩ := (functorVertexEquiv K (continuousKanReplacement.obj E)).surjective v'
  change SSet.π₀.mk (functorVertex (f ≫ continuousKanReplacement.map F)) =
    SSet.π₀.mk (functorVertex (g ≫ continuousKanReplacement.map F)) at h
  obtain ⟨H⟩ := (functorVertex_piZero_eq_iff_homotopy _ _).1 h
  exact (functorVertex_piZero_eq_iff_homotopy _ _).2
    (hF.kanFiniteDiagram_reflects_homotopy f g H)

/-- Kan 置換後の比較は、全ての有限パラメータの写像空間の連結成分上で全単射。 -/
lemma HasFiniteHomotopyRelativeFillers.kanFiniteDiagramPiZero_bijective
    {E Q : SSet.{u}} {F : E ⟶ Q} (hF : HasFiniteHomotopyRelativeFillers F)
    (K : SSet.{u}) [K.Finite] : Function.Bijective
      (SSet.mapπ₀ ((ihom K).map (continuousKanReplacement.map F))) :=
  ⟨hF.kanFiniteDiagramPiZero_injective K, hF.kanFiniteDiagramPiZero_surjective K⟩

end SerrePositivity.InfinityCategories
