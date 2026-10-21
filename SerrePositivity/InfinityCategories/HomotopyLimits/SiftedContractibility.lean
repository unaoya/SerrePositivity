module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SiftedInfinity
public import SerrePositivity.InfinityCategories.F1B.CofinalWeakEquivalence

/-!
概要：sifted 単体集合の弱可縮性を、対角によるホモトピー類の単射性から導く。
方針：二射影の像を対角で比較し、指定頂点と恒等射の組で制限して定値化する。
規約：元の添字に Kan 性・quasicategory 性を仮定しない。
使われ方：HTT 5.5.8.7、sifted 余極限による空積の保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 弱同値な二項対角を持つ底から Kan 標的への射は、指定頂点の値にホモトピック。 -/
lemma homotopy_const_of_weakDiagonal {K Z : SSet.{u}} [KanComplex Z]
    (hδ : IsWeakHomotopyEquivalence (lift (𝟙 K) (𝟙 K)))
    (k : K _⦋0⦌) (f : K ⟶ Z) :
    Nonempty (SSet.Homotopy f (SSet.const (f.app (Opposite.op ⦋0⦌) k))) := by
  have hp : SSet.π₀.mk (functorVertex (snd K K ≫ f)) =
      SSet.π₀.mk (functorVertex (fst K K ≫ f)) := by
    apply (hδ Z).injective
    change SSet.π₀.mk (functorVertex (lift (𝟙 K) (𝟙 K) ≫ (snd K K ≫ f))) =
      SSet.π₀.mk (functorVertex (lift (𝟙 K) (𝟙 K) ≫ (fst K K ≫ f)))
    rw [← Category.assoc, lift_snd, ← Category.assoc, lift_fst]
  have h := congrArg (SSet.mapπ₀
    ((pre (lift (SSet.const k : K ⟶ K) (𝟙 K))).app Z)) hp
  change SSet.π₀.mk (functorVertex (lift (SSet.const k) (𝟙 K) ≫ (snd K K ≫ f))) =
    SSet.π₀.mk (functorVertex (lift (SSet.const k) (𝟙 K) ≫ (fst K K ≫ f))) at h
  rw [← Category.assoc, lift_snd, Category.id_comp, ← Category.assoc, lift_fst,
    SSet.const_comp] at h
  exact (functorVertex_piZero_eq_iff_homotopy _ _).mp h

/-- 頂点を持ち二項対角が弱同値である単体集合は弱可縮。 -/
lemma isWeaklyContractible_of_nonempty_of_weakDiagonal {K : SSet.{u}}
    (hk : Nonempty (K _⦋0⦌))
    (hδ : IsWeakHomotopyEquivalence (lift (𝟙 K) (𝟙 K))) : IsWeaklyContractible K := by
  obtain ⟨k⟩ := hk
  intro Z hZ
  let q := terminal.from K
  let r : (⊤_ SSet.{u}) ⟶ K := SSet.const k
  have hl : Function.LeftInverse (SSet.mapπ₀ ((pre r).app Z))
      (SSet.mapπ₀ ((pre q).app Z)) := by
    intro a
    rw [← SSet.mapπ₀_comp_apply]
    have he : (pre q).app Z ≫ (pre r).app Z = 𝟙 ((ihom (⊤_ SSet.{u})).obj Z) := by
      rw [← NatTrans.comp_app, ← pre_map, show r ≫ q = 𝟙 _ from terminal.hom_ext _ _,
        pre_id]
      rfl
    rw [he, SSet.mapπ₀_id_apply]
  have hr : Function.RightInverse (SSet.mapπ₀ ((pre r).app Z))
      (SSet.mapπ₀ ((pre q).app Z)) := by
    intro a
    obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective a
    obtain ⟨f, rfl⟩ := (functorVertexEquiv K Z).surjective v
    change SSet.π₀.mk (functorVertex (q ≫ (r ≫ f))) = SSet.π₀.mk (functorVertex f)
    dsimp only [r]
    rw [SSet.const_comp, SSet.comp_const]
    exact ((functorVertex_piZero_eq_iff_homotopy _ _).mpr
      (homotopy_const_of_weakDiagonal hδ k f)).symm
  exact ⟨hl.injective, hr.surjective⟩

/-- HTT 5.5.8.7：sifted 単体集合は弱可縮。 -/
lemma isWeaklyContractible_of_sifted (K : SSet.{u}) [IsSiftedInfinity K] :
    IsWeaklyContractible K :=
  isWeaklyContractible_of_nonempty_of_weakDiagonal
    (IsSiftedInfinity.nonempty_vertices (K := K))
    (IsSiftedInfinity.diagonal_rightCofinal (K := K)).isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
